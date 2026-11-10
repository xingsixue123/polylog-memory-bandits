import Pool.P0156.GRun

/-!
# Design Z's member process with (b″) as RETIREMENT, as an instance of the generic process

P0136's Design Z evicts a member by rule (b″) at any round. In the threaded process (P0065 / P0095) copies leave the
pools only at merges. Here a (b″)-evicted member **retires** instead:
* (design intent, not modelled here) it is no longer played; its slot plays BASE, and it leaves ALG;
* it stays in its pools until its thread's next merge removes it (or longer);
* its cover data grow by a **fake increment `1` per unit** instead of slot observations.

Units are rounds, and `s` is the number of (virtual) slots, so an active member is observed with probability `1/s`
and its slot increment `s·L` is the importance-weighted estimate. The fake increment `1` dominates any per-round loss
in `[0, 1]`. So on a retired segment, a chain member's data upper-bound ALG's loss, and cover certificates need no
ALG regret there (`Lint_retired`).

* `foUpd`, `foRun_eq_gRun`: P0095's process is the generic process with `foUpd` (bridge).
* `zUpd`, `zRun`: the retirement process. The retirement rule `rh a x h` sees the unit, the copy, and the copy's own
  updated data history `h`, e.g. "(b″): its data since entry minus BASE's estimate exceed Λ".
* `zInc_bounds`: increments in `[0, s]` when `1 ≤ s` and losses lie in `[0, 1]`.
* `zInc_retired`, `zInc_active`, `mem_aux_succ`, `aux_mono`, `Lint_retired`: pathwise facts.
* `z_forced_erase`: the copy-last coupling (P0095's `fo_forced_erase`) for the retirement process; `z_free_eq`: its
  copy-free run is the entry-order (algorithm's) run.

Only the cover data, the pools and the retired set are modelled; ALG and BASE do not appear. All results are for a
FIXED slot sequence `y` and a FIXED rule `rh`. Averaging over them requires both to be independent of the sampling and
filter coins (e.g. `B̂` from BASE's own rounds only, not from plays on retired slots).
* **`prob_members_large_Z`**: P0109's pool-size bound for the retirement process.
-/

namespace Pool.P0156

open Finset Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0046 Pool.P0073 Pool.P0109

section Bridge

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι)
  (y : ℕ → Fin s)
/-- P0095's update: the copy in slot `y a` of the start pools gains `s·L`. -/
noncomputable def foUpd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Unit → (ι → ℝ) × Unit :=
  fun a sp _ _ => (fun x => if occ (members D Lv sp) (y a) = some x then (s : ℝ) * L a x else 0, ())
/-- **Bridge.** P0095's one-free-observation process is the generic process with `foUpd`. -/
theorem foRun_eq_gRun (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ∀ a,
    (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools =
        (gRun E thr0 θ R K D Lv Bt lev (foUpd D Lv s L occ y) () ωs φ a).pools ∧
      (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).est =
        (gRun E thr0 θ R K D Lv Bt lev (foUpd D Lv s L occ y) () ωs φ a).est := by
  intro a
  induction a with
  | zero => exact ⟨rfl, rfl⟩
  | succ a ih =>
    obtain ⟨hp, he⟩ := ih
    have hst : estStep s L a (occ (members D Lv (startPools E thr0 D Lv Bt ωs a
        (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools)) (y a))
          (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).est =
        gStep a (foUpd D Lv s L occ y a (startPools E thr0 D Lv Bt ωs a
          (gRun E thr0 θ R K D Lv Bt lev (foUpd D Lv s L occ y) () ωs φ a).pools)
          (gRun E thr0 θ R K D Lv Bt lev (foUpd D Lv s L occ y) () ωs φ a).est ()).1
          (gRun E thr0 θ R K D Lv Bt lev (foUpd D Lv s L occ y) () ωs φ a).est := by
      rw [hp, he]; rfl
    refine ⟨?_, ?_⟩
    · show (fun r => if Bt r ∣ a + 1 then _ else _) = (fun r => if Bt r ∣ a + 1 then _ else _)
      rw [hst, hp]
    · exact hst

end Bridge

section Z

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι)
  (y : ℕ → Fin s) (rh : ℕ → ι → (ℕ → ℝ) → Bool)
/-- The increments of the retirement process: `1` for retired copies, `s·L` for the observed active copy. -/
noncomputable def zIncr (a : ℕ) (sp : ℕ → ℕ → Finset ι) (ret : Finset ι) : ι → ℝ :=
  fun x => if x ∈ ret then 1 else if occ (members D Lv sp) (y a) = some x then (s : ℝ) * L a x else 0
/-- **The retirement update.** Members of the start pools whose updated own history triggers `rh` retire. -/
noncomputable def zUpd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι :=
  fun a sp est ret =>
    (zIncr D Lv s L occ y a sp ret,
     ret ∪ (members D Lv sp).filter (fun x => rh a x (gStep a (zIncr D Lv s L occ y a sp ret) est x) = true))
/-- **Design Z's member process** (with retirement): the generic process with `zUpd`, no copy retired at start. -/
noncomputable abbrev zRun (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ℕ → GSt ι (Finset ι) :=
  gRun E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ ωs φ

variable (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

theorem zInc_eq (a : ℕ) :
    gInc E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ ωs φ a =
      zIncr D Lv s L occ y a (startPools E thr0 D Lv Bt ωs a (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).pools)
        (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).aux := rfl
/-- Increments lie in `[0, s]`. -/
theorem zInc_bounds (hs : 1 ≤ s) (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (a : ℕ) (x : ι) :
    0 ≤ gInc E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ ωs φ a x ∧
      gInc E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ ωs φ a x ≤ s := by
  rw [zInc_eq]
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold zIncr
  split_ifs
  · exact ⟨zero_le_one, hs'⟩
  · exact ⟨mul_nonneg (by positivity) (hL0 a x), mul_le_of_le_one_right (by positivity) (hL1 a x)⟩
  · exact ⟨le_rfl, by positivity⟩
/-- A retired copy's data grow by exactly `1` per unit. -/
theorem zInc_retired (a : ℕ) {x : ι} (hx : x ∈ (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).aux) :
    gInc E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ ωs φ a x = 1 := by
  rw [zInc_eq]; unfold zIncr; rw [if_pos hx]
/-- An active copy's data grow by `s·L` when it is in the observed slot, and not at all otherwise. -/
theorem zInc_active (a : ℕ) {x : ι} (hx : x ∉ (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).aux) :
    gInc E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ ωs φ a x =
      if occ (members D Lv (startPools E thr0 D Lv Bt ωs a
          (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).pools)) (y a) = some x then (s : ℝ) * L a x else 0 := by
  rw [zInc_eq]; unfold zIncr; rw [if_neg hx]
/-- Retirement step: retired after unit `a` iff retired before, or a start-pool member whose own updated history
triggers `rh`. -/
theorem mem_aux_succ (a : ℕ) (x : ι) :
    x ∈ (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ (a + 1)).aux ↔
      x ∈ (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).aux ∨
        (x ∈ members D Lv (startPools E thr0 D Lv Bt ωs a (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).pools) ∧
          rh a x ((zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ (a + 1)).est x) = true) := by
  show x ∈ (zUpd D Lv s L occ y rh a _ _ _).2 ↔ _
  simp only [zUpd, Finset.mem_union, Finset.mem_filter]
  rfl
/-- Retirement is permanent. -/
theorem aux_mono {a b : ℕ} (hab : a ≤ b) {x : ι} (hx : x ∈ (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).aux) :
    x ∈ (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ b).aux := by
  induction b, hab using Nat.le_induction with
  | base => exact hx
  | succ b _ ih => exact (mem_aux_succ E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ b x).2 (Or.inl ih)
/-- **Retired segments.** If `x` is retired at unit `a`, its data over `[a, b)` equal the length `b − a`, which bounds
any loss in `[0, 1]` per round (ALG's included). -/
theorem Lint_retired {a b : ℕ} (hab : a ≤ b) {x : ι}
    (hx : x ∈ (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).aux) :
    Lint (gChat E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ ωs φ) x a b = ((b - a : ℕ) : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base => simp [Lint]
  | succ b hab ih =>
    unfold Lint at ih ⊢
    rw [gChat_succ, zInc_retired E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ b
      (aux_mono E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ hab hx)]
    rw [show b + 1 - a = (b - a) + 1 by omega]; push_cast; linarith
/-- With the never-retire rule nothing is ever retired. -/
theorem aux_noRetire : ∀ a, (zRun E thr0 θ R K D Lv Bt lev s L occ y (fun _ _ _ => false) ωs φ a).aux = ∅ := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    ext x
    rw [mem_aux_succ, ih]
    simp
/-- **Control: retirement disabled recovers P0095's process.** With the never-retire rule, the retirement process
has P0095's pools and data at every boundary. -/
theorem zRun_noRetire : ∀ a,
    (zRun E thr0 θ R K D Lv Bt lev s L occ y (fun _ _ _ => false) ωs φ a).pools =
        (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools ∧
      (zRun E thr0 θ R K D Lv Bt lev s L occ y (fun _ _ _ => false) ωs φ a).est =
        (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).est := by
  intro a
  induction a with
  | zero => exact ⟨rfl, rfl⟩
  | succ a ih =>
    obtain ⟨hp, he⟩ := ih
    have hst : gStep a (gInc E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y (fun _ _ _ => false)) ∅ ωs φ a)
          (zRun E thr0 θ R K D Lv Bt lev s L occ y (fun _ _ _ => false) ωs φ a).est =
        estStep s L a (occ (members D Lv (startPools E thr0 D Lv Bt ωs a
          (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools)) (y a))
          (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).est := by
      rw [zInc_eq, aux_noRetire, hp, he]
      funext x t
      simp only [gStep, estStep, zIncr, Finset.notMem_empty, if_false]
    refine ⟨?_, ?_⟩
    · rw [← gRun_succ_est] at hst
      have hst' : (gRun E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y (fun _ _ _ => false)) ∅ ωs φ (a + 1)).est =
          (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1)).est := hst
      funext r
      have h1 := gRun_succ_pools E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y (fun _ _ _ => false)) ∅ ωs φ a r
      have h2 := foRun_succ_pools E thr0 θ R K D Lv Bt lev s L occ ωs φ y a r
      exact (h1.trans (by rw [hst', hp])).trans h2.symm
    · exact hst

end Z

section Coupling

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (y : ℕ → Fin s)
  (rh : ℕ → ι → (ℕ → ℝ) → Bool)
/-- **Pathwise copy-last coupling for the retirement process** (P0095's `fo_forced_erase`). With the copy-last rule,
the run with a never-filter copy `c` forced in and the copy-free run have, at every boundary, the same pools up to `c`,
the same data for every other copy, and the same retired set up to `c`. Retirement reads only the copy's own data,
so `c` changes nobody else's retirement. -/
theorem z_forced_erase {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ∀ a,
    (∀ r ℓ, ((zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh (forceS ωs c) (forceF K φ c) a).pools r ℓ).erase c =
        (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh ωs φ a).pools r ℓ) ∧
      (∀ x, x ≠ c → ∀ t,
        (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh (forceS ωs c) (forceF K φ c) a).est x t =
          (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh ωs φ a).est x t) ∧
      (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh (forceS ωs c) (forceF K φ c) a).aux.erase c =
        (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh ωs φ a).aux.erase c := by
  classical
  have hs : AgreeOff c (forceS ωs c) ωs := fun x hx => by simp [forceS, Function.update_of_ne hx]
  intro a
  induction a with
  | zero => exact ⟨fun r ℓ => by simp [gRun], fun x _ t => rfl, rfl⟩
  | succ a ih =>
    obtain ⟨hP, hE, hA⟩ := ih
    set F := zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh (forceS ωs c) (forceF K φ c) with hF
    set G := zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh ωs φ with hG
    have hPfun : (fun r ℓ => ((F a).pools r ℓ).erase c) = (G a).pools := by
      funext r ℓ; exact hP r ℓ
    have hS : ∀ r ℓ, (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools r ℓ).erase c =
        startPools E thr0 D Lv Bt ωs a (G a).pools r ℓ := by
      intro r ℓ
      rw [startPools_erase c (forceS ωs c) ωs hs hc, hPfun]
    have hSfun : (fun r ℓ => (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools r ℓ).erase c) =
        startPools E thr0 D Lv Bt ωs a (G a).pools := funext fun r => funext fun ℓ => hS r ℓ
    -- observation
    have hobs : ∀ x, x ≠ c →
        ((occLast s c) (members D Lv (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools)) (y a) = some x ↔
          (occLast s c) (members D Lv (startPools E thr0 D Lv Bt ωs a (G a).pools)) (y a) = some x) := by
      intro x hx
      rw [occLast_erase s c _ (y a) hx, members_erase, hSfun]
    have hret : ∀ x, x ≠ c → (x ∈ (F a).aux ↔ x ∈ (G a).aux) := by
      intro x hx
      constructor
      · intro h; have : x ∈ (F a).aux.erase c := Finset.mem_erase.2 ⟨hx, h⟩
        rw [hA] at this; exact (Finset.mem_erase.1 this).2
      · intro h; have : x ∈ (G a).aux.erase c := Finset.mem_erase.2 ⟨hx, h⟩
        rw [← hA] at this; exact (Finset.mem_erase.1 this).2
    -- increments
    have hinc : ∀ x, x ≠ c →
        gInc E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occLast s c) y rh) ∅ (forceS ωs c) (forceF K φ c) a x =
          gInc E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occLast s c) y rh) ∅ ωs φ a x := by
      intro x hx
      rw [zInc_eq, zInc_eq]
      unfold zIncr
      by_cases h1 : x ∈ (G a).aux
      · rw [if_pos ((hret x hx).2 h1), if_pos h1]
      · rw [if_neg (fun h => h1 ((hret x hx).1 h)), if_neg h1]
        by_cases h2 : (occLast s c) (members D Lv (startPools E thr0 D Lv Bt ωs a (G a).pools)) (y a) = some x
        · rw [if_pos ((hobs x hx).2 h2), if_pos h2]
        · rw [if_neg (fun h => h2 ((hobs x hx).1 h)), if_neg h2]
    -- data
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
    · ext x
      by_cases hx : x = c
      · subst hx; simp
      simp only [Finset.mem_erase, hx, ne_eq, not_false_eq_true, true_and]
      rw [mem_aux_succ, mem_aux_succ, ← hF, ← hG, hret x hx]
      have hmem : x ∈ members D Lv (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools) ↔
          x ∈ members D Lv (startPools E thr0 D Lv Bt ωs a (G a).pools) := by
        rw [← hSfun, ← members_erase]
        simp [hx]
      have hest : (F (a + 1)).est x = (G (a + 1)).est x := funext fun t => hE' x hx t
      rw [hmem, hest]
/-- The copy-free run never contains the copy: its start pools' members never contain it. -/
theorem z_not_mem_members_free {c : ι} {ωs : ι → Bool} (hc : ωs c = false)
    (occ : Finset ι → Fin s → Option ι) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) :
    c ∉ members D Lv (startPools E thr0 D Lv Bt ωs a (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).pools) := by
  intro h
  simp only [members, Finset.mem_biUnion, Finset.mem_range] at h
  obtain ⟨r, -, ℓ, -, h⟩ := h
  have := Pool.P0083.mem_startPools_sampled E thr0 D Lv Bt ωs a _ (by
    rw [gRun_pools_eq]
    exact Pool.P0083.mem_tpools_sampled E thr0 θ R K D Lv Bt lev _ ωs φ a) r ℓ c h
  rw [hc] at this; exact Bool.false_ne_true this
/-- Without the copy among the members, the copy-last update is the entry-order update. -/
theorem zUpd_occLast_of_not_mem {c : ι} (a : ℕ) (sp : ℕ → ℕ → Finset ι) (est : ι → ℕ → ℝ) (ret : Finset ι)
    (hc : c ∉ members D Lv sp) :
    zUpd D Lv s L (occLast s c) y rh a sp est ret = zUpd D Lv s L (occSort s) y rh a sp est ret := by
  unfold zUpd zIncr
  rw [occLast_of_not_mem s hc]
/-- **The copy-free run of the coupling is the actual algorithm's run** (P0095's `foRun_free_eq` for the retirement
process): when `c` is never sampled (`ωs c = false`), the copy-last rule and the entry-order rule give the same run
(pools, data and retired set). -/
theorem z_free_eq {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ∀ a,
    zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh ωs φ a =
      zRun E thr0 θ R K D Lv Bt lev s L (occSort s) y rh ωs φ a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have hupd := zUpd_occLast_of_not_mem (D := D) (Lv := Lv) (s := s) (L := L) (y := y) (rh := rh) (c := c) a
      (startPools E thr0 D Lv Bt ωs a (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh ωs φ a).pools)
      (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh ωs φ a).est
      (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh ωs φ a).aux
      (z_not_mem_members_free E thr0 θ R K D Lv Bt lev s L y rh hc _ φ a)
    simp only [zRun, gRun] at ih hupd ⊢
    rw [hupd, ih]

end Coupling

section Sizes

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s)
  (rh : ℕ → ι → (ℕ → ℝ) → Bool) {NE Lt : ℕ} (M0 : ℝ) (kk : ℕ)

open Classical in
/-- **Pool sizes of Design Z's member process with retirement.** For every fixed slot sequence `y` and every
retirement rule `rh` (e.g. (b″) against a fixed BASE estimate sequence; averaging over `y` and that sequence needs them
independent of the sampling/filter coins), except with probability
`≤ NE·D·δs + NE·D·(Lt+1)·K·delta` over the sampling and filter coins, at every unit `a < NE` the start-pool members
number at most `D·((s0 + D·Lv·S) + (Lv−1)·S) + D·s0` (P0109's bound, `Tmax = s·NE`). -/
theorem prob_members_large_Z {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hE : Monotone E) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hs1 : 1 ≤ s) (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (hR : 1 ≤ R) (hT : (s : ℝ) * NE ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
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
            (zRun E thr0 θ R K D Lv Bt lev s L occ y rh (ωsOfT E K D ω) (φOfT K D ω) a).pools)).card : ℝ) ≤
              D * ((s0 + D * Lv * S) + (Lv - 1 : ℕ) * S) + D * s0
          then 0 else 1)
      ≤ NE * D * δs + NE * D * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 :=
  prob_members_large_gen E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ M0 kk hps hp0 hp1 hE hB hLv hlev
    (Nat.cast_nonneg s) (fun ωs φ a x => zInc_bounds E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ hs1 hL0 hL1 a x)
    hR hT hM0 hk hp hlevLt s0 δs hs S hM0S hS0 hρS

end Sizes

end Pool.P0156
