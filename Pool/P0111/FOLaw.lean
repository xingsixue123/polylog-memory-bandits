import Pool.P0105.FOConc
import Pool.P0070.Relabel

/-!
# The in-law step for the one-free-observation threaded process: entry order vs copy last

The algorithm lays out the start-pool members in entry order (`Pool.P0095.occSort`). The certificates and the
pathwise coupling (P0095, P0105) use the copy-last order (`Pool.P0095.occLast c`). Under i.i.d. uniform slots the two
runs have the same law on every event of the trajectory that includes "no overflow".

* `capOcc`: the capped layout (nothing observed on overflow); `compat_cap`: capped entry order and capped copy last
  are P0070-compatible at every member set (via `listOcc`, `compat_listOcc`).
* `obsStep`, `foRun_succ_obs`, `trStep`, `tr0`, `run_trStep`: the trajectory of `foRun` up to `T` is a P0070
  `run`, using P0105's causality in the slot draws.
* `traj_law`: compatible layouts give trajectories with the same law (P0070's `sum_run_eq`, with the permutation
  from `exists_perm`).
* `foRun_cap_eq`, `foRun_cap_eq'`, `NoOverflow`, `traj`, `traj_cap`: on overflow-free paths the cap is invisible.
* **`law_occSort_occLast`**: for every copy `c` and every event `G` of the trajectory up to `T`,
  `P(NoOverflow ∧ G)` is the same for the (uncapped) entry-order and copy-last runs.
* `wgt_eq_wR`: P0092's weight with uniform slots is P0070's `wR` with `μ ≡ 1/s`.
-/

namespace Pool.P0111

open Finset Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0105

section Law

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- The capped layout: nothing is observed when the members do not fit in the `s` slots. -/
def capOcc (occ : Finset ι → Fin s → Option ι) (V : Finset ι) (y : Fin s) : Option ι :=
  if V.card ≤ s then occ V y else none

/-- The start-pool members of a state at unit `a`. -/
noncomputable def Vst (a : ℕ) (st : FOSt ι) : Finset ι := members D Lv (startPools E thr0 D Lv Bt ωs a st.pools)

/-- One unit of the process, given the observed slot content `o`. -/
noncomputable def obsStep (a : ℕ) (st : FOSt ι) (o : Option ι) : FOSt ι :=
  ⟨fun r => if Bt r ∣ a + 1 then
      mergeUpTo E (estStep s L a o st.est) θ R K (φ r) a (lev r a) (startPools E thr0 D Lv Bt ωs a st.pools r)
    else startPools E thr0 D Lv Bt ωs a st.pools r,
   estStep s L a o st.est⟩

theorem foRun_succ_obs (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) (a : ℕ) :
    foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1) =
      obsStep E thr0 θ R K D Lv Bt lev s L ωs φ a (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a)
        (occ (Vst E thr0 D Lv Bt ωs a (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a)) (y a)) := rfl

/-- The trajectory step: keep the history up to `u`, append the state at `u + 1`. -/
noncomputable def trStep (occ : Finset ι → Fin s → Option ι) (u : ℕ) (tr : ℕ → FOSt ι) (y : Fin s) : ℕ → FOSt ι :=
  fun a => if a ≤ u then tr a else
    obsStep E thr0 θ R K D Lv Bt lev s L ωs φ u (tr u) (occ (Vst E thr0 D Lv Bt ωs u (tr u)) y)

/-- The initial trajectory. -/
def tr0 : ℕ → FOSt ι := fun _ => ⟨fun _ _ => ∅, fun _ _ => 0⟩

/-- **The trajectory is a P0070 `run`.** After `T` units with slots `ω`, the trajectory holds the FO states at all
boundaries `≤ T` (and the state at `T` after). -/
theorem run_trStep [NeZero s] (occ : Finset ι → Fin s → Option ι) : ∀ (T : ℕ) (ω : Fin T → Fin s) (a : ℕ),
    Pool.P0070.run (trStep E thr0 θ R K D Lv Bt lev s L ωs φ occ) tr0 T ω a =
      foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) (min a T)
  | 0, ω, a => by simp only [Pool.P0070.run, Nat.min_zero]; rfl
  | T + 1, ω, a => by
    have hc : ∀ b ≤ T, foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s (Fin.init ω)) b =
        foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) b := fun b hb =>
      foRun_congr_y E thr0 θ R K D Lv Bt lev s L occ ωs φ b (fun v hv => extY_init s ω v (by omega))
    simp only [Pool.P0070.run, trStep]
    split_ifs with ha
    · rw [run_trStep occ T (Fin.init ω) a, hc _ (by omega)]
      congr 1; omega
    · rw [run_trStep occ T (Fin.init ω) T, Nat.min_self, hc T le_rfl, show min a (T + 1) = T + 1 by omega,
        foRun_succ_obs, extY_last]

/-- The layout of a list in the first slots. -/
def listOcc {α : Type*} (s : ℕ) (Lst : List α) (y : Fin s) : Option α :=
  if h : y.1 < Lst.length then some Lst[y.1] else none

theorem listOcc_eq_some {α : Type*} {s : ℕ} {Lst : List α} {y : Fin s} {x : α} (h : listOcc s Lst y = some x) :
    ∃ h' : y.1 < Lst.length, Lst[y.1] = x := by
  unfold listOcc at h
  split_ifs at h with h1
  exact ⟨h1, Option.some.inj h⟩

/-- Two duplicate-free lists of length `≤ s` with the same elements are compatible layouts. -/
theorem compat_listOcc {α : Type*} {s : ℕ} (L1 L2 : List α) (h1 : L1.Nodup) (h2 : L2.Nodup)
    (hl1 : L1.length ≤ s) (hl2 : L2.length ≤ s) (hmem : ∀ x, x ∈ L1 ↔ x ∈ L2) :
    Pool.P0070.Compat (listOcc s L1) (listOcc s L2) := by
  have inj : ∀ (Lst : List α), Lst.Nodup → ∀ (y y' : Fin s) x, listOcc s Lst y = some x →
      listOcc s Lst y' = some x → y = y' := by
    intro Lst hn y y' x hy hy'
    obtain ⟨a, ha⟩ := listOcc_eq_some hy
    obtain ⟨b, hb⟩ := listOcc_eq_some hy'
    exact Fin.ext ((hn.getElem_inj_iff).mp (ha.trans hb.symm))
  have occ_iff : ∀ (Lst : List α), Lst.length ≤ s → ∀ x, (∃ y, listOcc s Lst y = some x) ↔ x ∈ Lst := by
    intro Lst hl x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨a, ha⟩ := listOcc_eq_some hy
      exact ha ▸ List.getElem_mem a
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exact ⟨⟨i, by omega⟩, by simp [listOcc, hi]⟩
  exact ⟨inj L1 h1, inj L2 h2, fun x => by rw [occ_iff L1 hl1, occ_iff L2 hl2, hmem]⟩

omit [Fintype ι] in
/-- **The capped entry-order and copy-last layouts are compatible at every member set.** -/
theorem compat_cap (c : ι) (V : Finset ι) :
    Pool.P0070.Compat (capOcc s (occLast s c) V) (capOcc s (occSort s) V) := by
  by_cases hV : V.card ≤ s
  · have e1 : capOcc s (occLast s c) V = listOcc s (lastList c V) := by
      funext y; simp only [capOcc, if_pos hV, occLast_eq_lastList, listOcc]
    have e2 : capOcc s (occSort s) V = listOcc s (V.sort (· ≤ ·)) := by
      funext y; simp only [capOcc, if_pos hV, occSort, listOcc]
    rw [e1, e2]
    refine compat_listOcc _ _ (lastList_nodup c V) (Finset.sort_nodup _ _) (by rw [lastList_length]; exact hV)
      (by rw [Finset.length_sort]; exact hV) fun x => ?_
    rw [← List.mem_toFinset, lastList_toFinset, Finset.mem_sort]
  · have e : ∀ occ : Finset ι → Fin s → Option ι, capOcc s occ V = fun _ => none := fun occ => by
      funext y; simp only [capOcc, if_neg hV]
    rw [e, e]
    exact ⟨fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h, fun _ => Iff.rfl⟩

/-- **Same law.** Two layout rules that are compatible at every member set give trajectories with the same law
under i.i.d. uniform slots. -/
theorem traj_law (occA occB : Finset ι → Fin s → Option ι) (hcompat : ∀ V, Pool.P0070.Compat (occA V) (occB V))
    (T : ℕ) (f : (ℕ → FOSt ι) → ℝ) :
    ∑ ω : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω *
        f (Pool.P0070.run (trStep E thr0 θ R K D Lv Bt lev s L ωs φ occB) tr0 T ω) =
      ∑ ω : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω *
        f (Pool.P0070.run (trStep E thr0 θ R K D Lv Bt lev s L ωs φ occA) tr0 T ω) := by
  choose τ hτ using fun V => Pool.P0070.exists_perm (occA V) (occB V) (hcompat V)
  refine Pool.P0070.sum_run_eq _ _ _ tr0 (fun u tr => τ (Vst E thr0 D Lv Bt ωs u (tr u))) ?_ (fun _ _ _ => rfl) T f
  intro u tr y
  funext a
  simp only [trStep, hτ]

/-- **The cap is invisible on overflow-free paths** (stated with the uncapped run's member sets). -/
theorem foRun_cap_eq (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) : ∀ a,
    (∀ u < a, (Vst E thr0 D Lv Bt ωs u (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y u)).card ≤ s) →
    foRun E thr0 θ R K D Lv Bt lev s L (capOcc s occ) ωs φ y a = foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    rw [foRun_succ_obs, foRun_succ_obs, ih (fun u hu => h u (by omega))]
    simp only [capOcc, if_pos (h a (by omega))]

/-- The same, stated with the capped run's member sets. -/
theorem foRun_cap_eq' (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) : ∀ a,
    (∀ u < a, (Vst E thr0 D Lv Bt ωs u (foRun E thr0 θ R K D Lv Bt lev s L (capOcc s occ) ωs φ y u)).card ≤ s) →
    foRun E thr0 θ R K D Lv Bt lev s L (capOcc s occ) ωs φ y a = foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have ih' := ih (fun u hu => h u (by omega))
    have ha := h a (by omega)
    rw [foRun_succ_obs, foRun_succ_obs, ih']
    rw [ih'] at ha
    simp only [capOcc, if_pos ha]

/-- No overflow before `T` along a trajectory. -/
def NoOverflow (T : ℕ) (tr : ℕ → FOSt ι) : Prop := ∀ u < T, (Vst E thr0 D Lv Bt ωs u (tr u)).card ≤ s

/-- The trajectory of a run up to `T` (frozen after `T`). -/
noncomputable def traj (occ : Finset ι → Fin s → Option ι) (T : ℕ) (y : ℕ → Fin s) : ℕ → FOSt ι :=
  fun a => foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (min a T)

theorem traj_cap (occ : Finset ι → Fin s → Option ι) (T : ℕ) (y : ℕ → Fin s) :
    (NoOverflow E thr0 D Lv Bt s ωs T (traj E thr0 θ R K D Lv Bt lev s L ωs φ (capOcc s occ) T y) ↔
      NoOverflow E thr0 D Lv Bt s ωs T (traj E thr0 θ R K D Lv Bt lev s L ωs φ occ T y)) ∧
    (NoOverflow E thr0 D Lv Bt s ωs T (traj E thr0 θ R K D Lv Bt lev s L ωs φ occ T y) →
      traj E thr0 θ R K D Lv Bt lev s L ωs φ (capOcc s occ) T y = traj E thr0 θ R K D Lv Bt lev s L ωs φ occ T y) := by
  have hmin : ∀ u < T, min u T = u := fun u hu => Nat.min_eq_left hu.le
  constructor
  · constructor
    · intro h u hu
      have h' : ∀ v < u, (Vst E thr0 D Lv Bt ωs v
          (foRun E thr0 θ R K D Lv Bt lev s L (capOcc s occ) ωs φ y v)).card ≤ s := fun v hv => by
        have := h v (by omega); simp only [traj, hmin v (by omega)] at this; exact this
      have := h u hu
      simp only [traj, hmin u hu] at this ⊢
      rwa [foRun_cap_eq' E thr0 θ R K D Lv Bt lev s L ωs φ occ y u h'] at this
    · intro h u hu
      have h' : ∀ v < u, (Vst E thr0 D Lv Bt ωs v
          (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y v)).card ≤ s := fun v hv => by
        have := h v (by omega); simp only [traj, hmin v (by omega)] at this; exact this
      have := h u hu
      simp only [traj, hmin u hu] at this ⊢
      rwa [foRun_cap_eq E thr0 θ R K D Lv Bt lev s L ωs φ occ y u h']
  · intro h
    funext a
    simp only [traj]
    refine foRun_cap_eq E thr0 θ R K D Lv Bt lev s L ωs φ occ y _ fun u hu => ?_
    have := h u (by omega)
    simp only [traj, hmin u (by omega)] at this
    exact this

open Classical in
/-- **In-law transfer between the actual entry-order run and the copy-last run.** For every copy `c` (sampled or
not) and every event `G` of the trajectory up to `T`: under i.i.d. uniform slots, the probability of {no overflow
before `T` and `G`} is the same for the entry-order rule `occSort` (the algorithm) and the copy-last rule `occLast c`.
Both runs are uncapped; the cap is used only inside the proof. -/
theorem law_occSort_occLast [NeZero s] (c : ι) (T : ℕ) (G : (ℕ → FOSt ι) → Prop) :
    ∑ ω : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω *
        (if NoOverflow E thr0 D Lv Bt s ωs T (traj E thr0 θ R K D Lv Bt lev s L ωs φ (occSort s) T (extY s ω)) ∧
            G (traj E thr0 θ R K D Lv Bt lev s L ωs φ (occSort s) T (extY s ω)) then 1 else 0) =
      ∑ ω : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω *
        (if NoOverflow E thr0 D Lv Bt s ωs T (traj E thr0 θ R K D Lv Bt lev s L ωs φ (occLast s c) T (extY s ω)) ∧
            G (traj E thr0 θ R K D Lv Bt lev s L ωs φ (occLast s c) T (extY s ω)) then 1 else 0) := by
  set f : (ℕ → FOSt ι) → ℝ := fun tr => if NoOverflow E thr0 D Lv Bt s ωs T tr ∧ G tr then 1 else 0 with hf
  have hrun : ∀ (occ : Finset ι → Fin s → Option ι) (ω : Fin T → Fin s),
      Pool.P0070.run (trStep E thr0 θ R K D Lv Bt lev s L ωs φ occ) tr0 T ω =
        traj E thr0 θ R K D Lv Bt lev s L ωs φ occ T (extY s ω) := fun occ ω => by
    funext a; exact run_trStep E thr0 θ R K D Lv Bt lev s L ωs φ occ T ω a
  have hcap : ∀ (occ : Finset ι → Fin s → Option ι) (ω : Fin T → Fin s),
      f (traj E thr0 θ R K D Lv Bt lev s L ωs φ (capOcc s occ) T (extY s ω)) =
        f (traj E thr0 θ R K D Lv Bt lev s L ωs φ occ T (extY s ω)) := by
    intro occ ω
    obtain ⟨hiff, heq⟩ := traj_cap E thr0 θ R K D Lv Bt lev s L ωs φ occ T (extY s ω)
    by_cases h : NoOverflow E thr0 D Lv Bt s ωs T (traj E thr0 θ R K D Lv Bt lev s L ωs φ occ T (extY s ω))
    · rw [heq h]
    · have h1 : ¬ (NoOverflow E thr0 D Lv Bt s ωs T
          (traj E thr0 θ R K D Lv Bt lev s L ωs φ (capOcc s occ) T (extY s ω)) ∧
          G (traj E thr0 θ R K D Lv Bt lev s L ωs φ (capOcc s occ) T (extY s ω))) := fun h' => h (hiff.mp h'.1)
      have h2 : ¬ (NoOverflow E thr0 D Lv Bt s ωs T (traj E thr0 θ R K D Lv Bt lev s L ωs φ occ T (extY s ω)) ∧
          G (traj E thr0 θ R K D Lv Bt lev s L ωs φ occ T (extY s ω))) := fun h' => h h'.1
      simp only [hf, if_neg h1, if_neg h2]
  have hlaw := traj_law E thr0 θ R K D Lv Bt lev s L ωs φ (capOcc s (occLast s c)) (capOcc s (occSort s))
    (compat_cap s c) T f
  simp only [hrun, hcap] at hlaw
  exact hlaw

/-- P0092's coin weight with uniform slots is P0070's `wR` with `μ ≡ 1/s`. -/
theorem wgt_eq_wR {s : ℕ} (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s) {T : ℕ} (ω : Fin T → Fin s) :
    Pool.P0092.wgt ν ω = Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω := by
  unfold Pool.P0092.wgt Pool.P0070.wR
  exact Finset.prod_congr rfl fun j _ => hν (ω j)

end Law

end Pool.P0111
