import Pool.P0156.ZRun
import Pool.P0135.WalkB

/-!
# Design Z's retirement process satisfies P0135's walk hypotheses `HypB`

P0135's walk (records ending by a cover at a merge, by rule (b″) at an arbitrary round, or bad; finest continuous
copies off the grid) assumes outcome functions `t τ r`, `g u` satisfying `HypB`. P0135 notes that no concrete process
is shown to satisfy it. Here: the outcomes of comparator copies forced into P0156's generic adapted-data process
(`gRun`, e.g. the retirement process `zRun`) do.

* Walk levels are the threads `0..D-2` (P0135's `R = D - 1`, `B = Bt`). Thread `D - 1` (epoch one unit) is a
  **holding thread**: it draws no filters (`φ (D-1) ≡ false`), so it removes nothing, and its copies (the finest
  continuous arrivals, one opportunity per unit) wait there until the next level-`(D-2)` boundary, where P0065's
  inheritance moves them to `canonT`.
* Outcome of a forced copy `c` (`outZ`): retired first (at a boundary `e`, `c ∈ aux`) → `bev e (min (curT c e) (D-2))`;
  removed from every pool first (at `e`) → `cov e`; neither before `T` → `bad`.
-/

namespace Pool.P0168

open Finset Pool.P0156 Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ)
  (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι) (aux0 : Finset ι)

/-- The run with copy `c` forced in as a never-filter copy. -/
noncomputable abbrev fRun (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : ℕ → GSt ι (Finset ι) :=
  gRun E thr0 θ R K D Lv Bt lev upd aux0 (forceS ωs c) (forceF K φ c)

/-- Its realized data. -/
noncomputable abbrev fChat (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : ι → ℕ → ℝ :=
  gChat E thr0 θ R K D Lv Bt lev upd aux0 (forceS ωs c) (forceF K φ c)

/-- First boundary in `(E c, T]` at which the forced copy is retired. -/
noncomputable def retT (T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : Option ℕ :=
  open Classical in
  if h : ∃ y, E c < y ∧ y ≤ T ∧ c ∈ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c y).aux then some (Nat.find h)
  else none

/-- First boundary in `(E c, T]` at which the forced copy is in no pool. -/
noncomputable def remT (T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : Option ℕ :=
  open Classical in
  if h : ∃ y, E c < y ∧ y ≤ T ∧ ¬ ∃ r ℓ, c ∈ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c y).pools r ℓ then
    some (Nat.find h)
  else none

/-- Outcome of the forced copy in P0135's form. Retirement takes precedence at equal times. The reported thread of a
(b″)-end is the copy's current thread after the inheritance at `e`, capped at `jmax` (`D - 1` on the unit grid,
`D - 2` with a holding thread). -/
noncomputable def outZ (jmax T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : Pool.P0135.Out :=
  match retT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c, remT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c with
  | some e, none => .bev e (min (curT E thr0 D Bt c e) jmax)
  | some e, some e' => if e ≤ e' then .bev e (min (curT E thr0 D Bt c e) jmax) else .cov e'
  | none, some e' => .cov e'
  | none, none => .bad

variable {E thr0 θ R K D Lv Bt lev upd aux0}

section Basic

lemma fRun_pools (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) (a : ℕ) :
    (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c a).pools =
      tpools E thr0 (fChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c) θ R K D Lv Bt lev (forceS ωs c)
        (forceF K φ c) a :=
  gRun_pools_eq E thr0 θ R K D Lv Bt lev upd aux0 _ _ a

/-- Specification of a removal outcome (P0065's removal schedule on the forced run's own data). -/
lemma remT_spec (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ} {ωs : ι → Bool}
    {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c) {e : ℕ}
    (he : remT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e) :
    E c < e ∧ e ≤ T ∧
      (∀ y, E c < y → y < e → Alive E thr0 (fChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c) θ R K D Lv Bt lev
        (forceS ωs c) (forceF K φ c) y c) ∧
      ∃ x, x + 1 = e ∧ E c ≤ x ∧
        SAlive E thr0 (fChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c) θ R K D Lv Bt lev (forceS ωs c)
          (forceF K φ c) x c ∧
        ¬ Alive E thr0 (fChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c) θ R K D Lv Bt lev (forceS ωs c)
          (forceF K φ c) e c ∧
        Bt (curT E thr0 D Bt c x) ∣ e := by
  classical
  set C := fChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c with hC
  have hal : ∀ y, Alive E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) y c ↔
      ∃ r ℓ, c ∈ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c y).pools r ℓ := by
    intro y; rw [fRun_pools]; rfl
  unfold remT at he
  split_ifs at he with h
  simp only [Option.some.injEq] at he
  obtain ⟨hae, heT, hna⟩ := he ▸ Nat.find_spec h
  have hmin : ∀ y, E c < y → y < e → Alive E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) y c := by
    intro y h1 h2
    rw [hal]
    by_contra hc'
    exact Nat.find_min h (he ▸ h2) ⟨h1, by omega, hc'⟩
  have hna' : ¬ Alive E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) e c := by rw [hal]; exact hna
  have hs0 : SAlive E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) (E c) c :=
    salive_entry hD hLv (by simp [forceS]) hthr hent
  obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := removal_dvd hD hLv hlev hs0 e hae hna'
  have hxe : x + 1 = e := by
    by_contra hne
    exact hx4 (hmin (x + 1) (by omega) (by omega))
  subst hxe
  exact ⟨hae, heT, hmin, x, rfl, hx1, hx3, hx4, hx5⟩

lemma retT_spec {T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} {e : ℕ}
    (he : retT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e) :
    E c < e ∧ e ≤ T ∧ c ∈ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c e).aux ∧
      ∀ y, E c < y → y < e → c ∉ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c y).aux := by
  classical
  unfold retT at he
  split_ifs at he with h
  simp only [Option.some.injEq] at he
  obtain ⟨hae, heT, hin⟩ := he ▸ Nat.find_spec h
  refine ⟨hae, heT, hin, fun y h1 h2 hy => Nat.find_min h (he ▸ h2) ⟨h1, by omega, hy⟩⟩

end Basic

section Pen

variable (E θ) (C : ι → ℕ → ℝ)

/-- With no filter (all bits false) a merge iteration removes nothing: the empty set covers nothing. -/
lemma mstep_false {t L : ℕ} {Q : Finset ι} {c : ι} (hc : c ∈ Q) :
    c ∈ mstep E C t θ L Q (fun _ => false) := by
  classical
  unfold mstep filterRound
  refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hc, ?_⟩)
  rintro ⟨ch, -, hmem, hok, -⟩
  have hF : Fof Q (fun _ => false) = ∅ := by
    ext x; simp [Fof]
  cases ch with
  | nil => exact hok
  | cons f rest =>
    have := hmem f (List.mem_cons_self ..)
    rw [hF] at this; simp at this

lemma iter_false {t : ℕ} {Q : Finset ι} {c : ι} (hc : c ∈ Q) :
    ∀ (m : ℕ) (ω : Fin m → ι → Bool), (∀ k x, ω k x = false) → c ∈ iter (mstep E C t θ R) Q m ω
  | 0, ω, _ => hc
  | m + 1, ω, hω => by
    simp only [iter]
    have h1 := iter_false (t := t) hc m (Fin.init ω) (fun k x => hω _ x)
    have : ω (Fin.last m) = fun _ => false := funext fun x => hω _ x
    rw [this]
    exact mstep_false E θ C h1

/-- A merge with all filter bits false keeps every copy (in some level). -/
lemma mem_mergeUpTo_false {φ : ℕ → ℕ → Fin K → ι → Bool} (hφ : ∀ a ℓ k x, φ a ℓ k x = false) {a : ℕ} :
    ∀ (m : ℕ) (P : ℕ → Finset ι) (j : ℕ) (c : ι), c ∈ P j → ∃ j', c ∈ mergeUpTo E C θ R K φ a m P j' := by
  have one : ∀ (ℓ : ℕ) (P : ℕ → Finset ι) (j : ℕ) (c : ι), c ∈ P j →
      ∃ j', c ∈ mergeOne E C θ R K φ a ℓ P j' := by
    intro ℓ P j c hc
    by_cases hj : j = ℓ ∨ j = ℓ + 1
    · refine ⟨ℓ + 1, ?_⟩
      unfold mergeOne
      rw [Function.update_of_ne (by omega), Function.update_self]
      refine iter_false E θ C (R := R) ?_ K (φ a ℓ) (fun k x => hφ a ℓ k x)
      rcases hj with rfl | rfl
      · exact Finset.mem_union_right _ hc
      · exact Finset.mem_union_left _ hc
    · refine ⟨j, ?_⟩
      unfold mergeOne
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hc
  intro m
  induction m with
  | zero => intro P j c hc; exact one 0 P j c hc
  | succ m ih =>
    intro P j c hc
    obtain ⟨j', hj'⟩ := ih P j c hc
    exact one (m + 1) _ j' c hj'

variable {E θ C}

/-- **Holding thread.** If thread `D - 1` draws no filters, a copy removed at the boundary `x + 1` was not in thread
`D - 1` at unit `x`. -/
lemma curT_lt_of_removed (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} (hpen : ∀ a ℓ k x, φ (D - 1) a ℓ k x = false)
    {c : ι} {x : ℕ}
    (hs : SAlive E thr0 C θ R K D Lv Bt lev ωs φ x c)
    (hn : ¬ Alive E thr0 C θ R K D Lv Bt lev ωs φ (x + 1) c) : curT E thr0 D Bt c x < D - 1 := by
  have hD := hB.hD
  obtain ⟨r, ℓ, hc⟩ := hs
  have hS := start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv
    (tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := C) (θ := θ) (R := R) (lev := lev)
      hD hLv hlev ωs φ x) ωs (x := x)
  obtain ⟨-, hr, -, hrD⟩ := hS c r ℓ hc
  by_contra hge
  have hrD1 : r = D - 1 := by omega
  obtain ⟨j', hj'⟩ := mem_mergeUpTo_false E θ C (R := R) (K := K) (φ := φ r)
    (fun a ℓ k z => by rw [hrD1]; exact hpen a ℓ k z) (a := x) (lev r x) _ ℓ c hc
  apply hn
  refine ⟨r, j', ?_⟩
  simp only [tpools]
  rw [if_pos (by rw [hrD1, hB.last]; exact one_dvd _)]
  exact hj'

end Pen

section Hyp

variable {jmax T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}

lemma outZ_cov {c : ι} {e : ℕ} (h : outZ E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c = .cov e) :
    remT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e ∧
      ∀ e0, retT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e0 → e < e0 := by
  unfold outZ at h
  split at h
  · cases h
  · rename_i e1 e2 h1 h2
    split_ifs at h with hle
    cases h
    exact ⟨h2, fun e0 he0 => by rw [h1] at he0; cases he0; omega⟩
  · rename_i e2 h1 h2
    cases h
    exact ⟨h2, fun e0 he0 => by rw [h1] at he0; cases he0⟩
  · cases h

lemma outZ_bev {c : ι} {e j : ℕ} (h : outZ E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c = .bev e j) :
    retT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e ∧ j = min (curT E thr0 D Bt c e) jmax ∧
      ∀ e', remT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e' → e ≤ e' := by
  unfold outZ at h
  split at h
  · rename_i e1 h1 h2
    cases h
    exact ⟨h1, rfl, fun e' he' => by rw [h2] at he'; cases he'⟩
  · rename_i e1 e2 h1 h2
    split_ifs at h with hle
    cases h
    exact ⟨h1, rfl, fun e' he' => by rw [h2] at he'; cases he'; exact hle⟩
  · cases h
  · cases h

lemma nob_of_le_curT (c : ι) {e j i m : ℕ} (hj : j ≤ curT E thr0 D Bt c e) (hi : i < j) (hm : Bt i ∣ m)
    (h1 : E c < m) (h2 : m ≤ e) : False := by
  have h3 := curT_mono (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c h2 (by omega)
  have h4 := curT_le_canonT (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c h1 (le_refl m)
  have h5 := canonT_le_of_dvd (D := D) hm
  omega

/-- A covered outcome satisfies P0065's removal schedule (P0057's `lb`, `edvd`, `align`). -/
lemma cov_sched (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι} {e : ℕ}
    (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c)
    (h : outZ E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c = .cov e) :
    E c < e ∧ e ≤ T ∧ Bt (thr0 c) ∣ e ∧ E c + Bt (thr0 c) ≤ e ∧
      (∀ i m, i < thr0 c → Bt i ∣ m → E c < m → m < e → Bt i ∣ e) ∧
      ∃ x, x + 1 = e ∧ Bt (curT E thr0 D Bt c x) ∣ e ∧
        SAlive E thr0 (fChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c) θ R K D Lv Bt lev
          (forceS ωs c) (forceF K φ c) x c ∧
        ¬ Alive E thr0 (fChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c) θ R K D Lv Bt lev
          (forceS ωs c) (forceF K φ c) e c := by
  obtain ⟨hev, -⟩ := outZ_cov h
  obtain ⟨hae, heT, -, x, hxe, hx1, hxs, hxn, hrem⟩ := remT_spec hB.hD hLv hlev hthr hent hev
  have := removal_hyp (E := E) (thr0 := thr0) (D := D) (Bt := Bt) hB (c := c) hthr hent (x := x) hx1 (hxe ▸ hrem)
  rw [hxe] at this
  exact ⟨hae, heT, this.1, this.2.1, this.2.2, x, hxe, hrem, hxs, hxn⟩

/-- **Per-copy version of `hypB_outZ_grid`**: each comparator copy `c` may be read from its own run, with its own
update rule `U c` and initial auxiliary state `A c` (e.g. P0156's copy-last layout `occLast c`, as P0156's
`z_forced_erase` and P0112-type walks need). **On the unit grid (P0166's design): the outcomes satisfy P0135's `HypB`** with walk levels = all threads
(`R = D`, `B = Bt`, finest epoch one unit), and no free copies (`g` constantly `bad`, never used by the walk since every
end is on the grid). `t τ r` is the outcome of the forced copy `cstar r τ`. -/
theorem hypB_outZ_grid_each (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι) (A : ι → Finset ι)
    (hE : ∀ j a, j < D → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j < D → Bt j ∣ a → a < T → thr0 (cstar j a) = j) :
    Pool.P0135.HypB D T Bt
      (fun τ r => outZ E thr0 θ R K D Lv Bt lev (U (cstar r τ)) (A (cstar r τ)) (D - 1) T ωs φ (cstar r τ))
      (fun _ => .bad) := by
  have hD := hB.hD
  have hc : ∀ j a e, j < D → Bt j ∣ a → a < T →
      outZ E thr0 θ R K D Lv Bt lev (U (cstar j a)) (A (cstar j a)) (D - 1) T ωs φ (cstar j a) = .cov e → _ :=
    fun j a e hj hd haT h => by
      have hE' := hE j a hj hd haT
      have hthr' := hthr j a hj hd haT
      have := cov_sched hB hLv hlev (by rw [hthr']; exact hj) (by rw [hthr', hE']; exact hd) h
      rw [hthr', hE'] at this
      exact this
  refine
    { pos := hB.pos
      dvd := fun r hr => hB.dvd r hr
      hR := hD
      hT := hT
      lb := fun τ r e hd hτ hr h => (hc r τ e hr hd hτ h).2.2.2.1
      ub := fun τ r e hd hτ hr h => (hc r τ e hr hd hτ h).2.1
      edvd := fun τ r e hd hτ hr h => (hc r τ e hr hd hτ h).2.2.1
      align := fun τ r e hd hτ hr h => (hc r τ e hr hd hτ h).2.2.2.2.1
      blt := ?_
      bnc := ?_
      flt := fun _ _ _ h => by cases h
      falign := fun _ _ _ h => by cases h
      fblt := fun _ _ _ _ h => by cases h
      fbnc := fun _ _ _ _ h => by cases h }
  · intro τ r e j hd hτ hr h
    obtain ⟨hev, rfl, -⟩ := outZ_bev h
    have hE' := hE r τ hr hd hτ
    have hthr' := hthr r τ hr hd hτ
    obtain ⟨hae, heT, -⟩ := retT_spec hev
    refine ⟨hE' ▸ hae, heT, ?_⟩
    have := curT_le_thr0 (E := E) (thr0 := thr0) (D := D) (Bt := Bt) (cstar r τ) e
    rw [hthr'] at this
    omega
  · intro τ r e j hd hτ hr h i m hi hm h1 h2
    obtain ⟨-, rfl, -⟩ := outZ_bev h
    have hE' := hE r τ hr hd hτ
    exact nob_of_le_curT (cstar r τ) (min_le_left _ _) hi hm (by rw [hE']; exact h1) h2

/-- **Per-copy version of `hypB_outZ`** (update rule `U c`, initial auxiliary state `A c` per copy). **With finest continuous arrivals (P0131/P0135's design): the outcomes satisfy `HypB`.** Walk levels are the
threads `0..D-2` (`R = D - 1`); thread `D - 1` (epoch one unit) is a holding thread that draws no filters
(`hpen`). `t τ r` is the outcome of `cstar r τ`, `g u` that of `cstar (D - 1) u`. -/
theorem hypB_outZ_each (hB : BtHyp D Bt) (hD2 : 2 ≤ D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι) (A : ι → Finset ι)
    (hE : ∀ j a, j < D → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j < D → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (hpen : ∀ a ℓ k x, φ (D - 1) a ℓ k x = false) :
    Pool.P0135.HypB (D - 1) T Bt
      (fun τ r => outZ E thr0 θ R K D Lv Bt lev (U (cstar r τ)) (A (cstar r τ)) (D - 2) T ωs φ (cstar r τ))
      (fun u => outZ E thr0 θ R K D Lv Bt lev (U (cstar (D - 1) u)) (A (cstar (D - 1) u)) (D - 2) T ωs φ (cstar (D - 1) u)) := by
  have hD := hB.hD
  have hc : ∀ j a e, j < D → Bt j ∣ a → a < T →
      outZ E thr0 θ R K D Lv Bt lev (U (cstar j a)) (A (cstar j a)) (D - 2) T ωs φ (cstar j a) = .cov e → _ :=
    fun j a e hj hd haT h => by
      have hE' := hE j a hj hd haT
      have hthr' := hthr j a hj hd haT
      have := cov_sched hB hLv hlev (by rw [hthr']; exact hj) (by rw [hthr', hE']; exact hd) h
      rw [hthr', hE'] at this
      exact this
  have hd1 : ∀ u, Bt (D - 1) ∣ u := fun u => by rw [hB.last]; exact one_dvd u
  refine
    { pos := hB.pos
      dvd := fun r hr => hB.dvd r (by omega)
      hR := by omega
      hT := hT
      lb := fun τ r e hd hτ hr h => (hc r τ e (by omega) hd hτ h).2.2.2.1
      ub := fun τ r e hd hτ hr h => (hc r τ e (by omega) hd hτ h).2.1
      edvd := fun τ r e hd hτ hr h => (hc r τ e (by omega) hd hτ h).2.2.1
      align := fun τ r e hd hτ hr h => (hc r τ e (by omega) hd hτ h).2.2.2.2.1
      blt := ?_
      bnc := ?_
      flt := ?_
      falign := fun u e hu h j m hj hm h1 h2 => (hc (D - 1) u e (by omega) (hd1 u) hu h).2.2.2.2.1 j m (by omega) hm h1 h2
      fblt := ?_
      fbnc := ?_ }
  · intro τ r e j hd hτ hr h
    obtain ⟨hev, rfl, -⟩ := outZ_bev h
    have hE' := hE r τ (by omega) hd hτ
    have hthr' := hthr r τ (by omega) hd hτ
    obtain ⟨hae, heT, -⟩ := retT_spec hev
    refine ⟨hE' ▸ hae, heT, ?_⟩
    have := curT_le_thr0 (E := E) (thr0 := thr0) (D := D) (Bt := Bt) (cstar r τ) e
    rw [hthr'] at this
    omega
  · intro τ r e j hd hτ hr h i m hi hm h1 h2
    obtain ⟨-, rfl, -⟩ := outZ_bev h
    have hE' := hE r τ (by omega) hd hτ
    exact nob_of_le_curT (cstar r τ) (min_le_left _ _) hi hm (by rw [hE']; exact h1) h2
  · intro u e hu h
    obtain ⟨hae, heT, -, -, -, x, hxe, hrem, hxs, hxn⟩ := hc (D - 1) u e (by omega) (hd1 u) hu h
    refine ⟨hae, heT, ?_⟩
    have hpen' : ∀ a ℓ k z, forceF K φ (cstar (D - 1) u) (D - 1) a ℓ k z = false := by
      intro a ℓ k z; unfold forceF; split_ifs
      · rfl
      · exact hpen a ℓ k z
    have hlt := curT_lt_of_removed hB hLv hlev hpen' hxs (hxe ▸ hxn)
    exact (hB.dvd_of_le (show curT E thr0 D Bt (cstar (D - 1) u) x ≤ D - 1 - 1 by omega)
      (by omega)).trans hrem
  · intro u e j hu h
    obtain ⟨hev, rfl, -⟩ := outZ_bev h
    have hE' := hE (D - 1) u (by omega) (hd1 u) hu
    obtain ⟨hae, heT, -⟩ := retT_spec hev
    exact ⟨hE' ▸ hae, heT, by omega⟩
  · intro u e j hu h i m hi hm h1 h2
    obtain ⟨-, rfl, -⟩ := outZ_bev h
    have hE' := hE (D - 1) u (by omega) (hd1 u) hu
    exact nob_of_le_curT (cstar (D - 1) u) (min_le_left _ _) hi hm (by rw [hE']; exact h1) h2

/-- **On the unit grid (P0166's design): the outcomes satisfy P0135's `HypB`** with walk levels = all threads
(`R = D`, `B = Bt`, finest epoch one unit), and no free copies (`g` constantly `bad`, never used by the walk since every
end is on the grid). `t τ r` is the outcome of the forced copy `cstar r τ`; one update rule for all copies (see
`hypB_outZ_grid_each` for one rule per copy). -/
theorem hypB_outZ_grid (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < D → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j < D → Bt j ∣ a → a < T → thr0 (cstar j a) = j) :
    Pool.P0135.HypB D T Bt
      (fun τ r => outZ E thr0 θ R K D Lv Bt lev upd aux0 (D - 1) T ωs φ (cstar r τ))
      (fun _ => .bad) :=
  hypB_outZ_grid_each hB hLv hlev hT cstar (fun _ => upd) (fun _ => aux0) hE hthr

/-- **With finest continuous arrivals (P0131/P0135's design): the outcomes satisfy `HypB`** (one update rule for all
copies; see `hypB_outZ_each`). Walk levels are the threads `0..D-2` (`R = D - 1`); thread `D - 1` (epoch one unit) is a
holding thread that draws no filters (`hpen`). The reported thread of a (b″)-end is capped at `D - 2`. -/
theorem hypB_outZ (hB : BtHyp D Bt) (hD2 : 2 ≤ D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < D → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j < D → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (hpen : ∀ a ℓ k x, φ (D - 1) a ℓ k x = false) :
    Pool.P0135.HypB (D - 1) T Bt
      (fun τ r => outZ E thr0 θ R K D Lv Bt lev upd aux0 (D - 2) T ωs φ (cstar r τ))
      (fun u => outZ E thr0 θ R K D Lv Bt lev upd aux0 (D - 2) T ωs φ (cstar (D - 1) u)) :=
  hypB_outZ_each hB hD2 hLv hlev hT cstar (fun _ => upd) (fun _ => aux0) hE hthr hpen

end Hyp


section Certificates

variable {jmax T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}

/-- P0065: a copy in the start pools of unit `x`, absent at `x + 1`, was removed by a merge of its current thread and
was covered at time `x + 1` by filters drawn from start-pool members of that thread. -/
lemma covered_of_removed_tpools {C : ι → ℕ → ℝ} (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    {ωs' : ι → Bool} {φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool} {x : ℕ} {c : ι}
    (hs : SAlive E thr0 C θ R K D Lv Bt lev ωs' φ' x c)
    (hn : ¬ Alive E thr0 C θ R K D Lv Bt lev ωs' φ' (x + 1) c) :
    Bt (curT E thr0 D Bt c x) ∣ x + 1 ∧
      ∃ Q' : Finset ι, (∀ z ∈ Q', ∃ j, z ∈ startPools E thr0 D Lv Bt ωs' x
          (tpools E thr0 C θ R K D Lv Bt lev ωs' φ' x) (curT E thr0 D Bt c x) j) ∧
        ∃ y : ι → Bool, c ∈ Q' ∧ c ∉ Fof Q' y ∧ Covered E C (x + 1) θ (Fof Q' y) c R := by
  obtain ⟨r, ℓ, hc⟩ := hs
  have hS := start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv
    (tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := C) (θ := θ) (R := R) (lev := lev)
      hD hLv hlev ωs' φ' x) ωs' (x := x)
  obtain ⟨-, hr, -, -⟩ := hS c r ℓ hc
  have hdvd : Bt (curT E thr0 D Bt c x) ∣ x + 1 := by
    by_contra hnd
    exact hn (alive_succ_of_not_dvd hD hLv ⟨r, ℓ, hc⟩ hlev hnd)
  refine ⟨hdvd, ?_⟩
  have hgone : ∀ j, c ∉ mergeUpTo E C θ R K (φ' r) x (lev r x)
      (startPools E thr0 D Lv Bt ωs' x (tpools E thr0 C θ R K D Lv Bt lev ωs' φ' x) r) j := by
    intro j hj
    apply hn
    refine ⟨r, j, ?_⟩
    simp only [tpools]
    rw [if_pos (hr ▸ hdvd)]
    exact hj
  obtain ⟨Q', hQ', y, h1, h2, h3⟩ := covered_of_removed_mergeUpTo (E := E) (C := C) (θ := θ) (R := R)
    (K := K) (φ := φ' r) (a := x) (lev r x) _ ⟨ℓ, hc⟩ hgone
  exact ⟨Q', fun z hz => by rw [← hr]; exact hQ' z hz, y, h1, h2, h3⟩

/-- **Certificate of a covered outcome.** The forced copy is never retired on `(E c, e]`, is alive on `(E c, e)`, and
at time `e` it is covered (P0030's `Covered`, margin `θ`, at most `R` pieces) on the forced run's own data by a filter
set drawn from start-pool members of its current thread at unit `e - 1`. -/
theorem cov_certZ (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι}
    (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c) {e : ℕ}
    (h : outZ E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c = .cov e) :
    E c < e ∧ e ≤ T ∧
      (∀ y, E c < y → y ≤ e → c ∉ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c y).aux) ∧
      (∀ y, E c < y → y < e → ∃ r ℓ, c ∈ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c y).pools r ℓ) ∧
      ∃ x, x + 1 = e ∧ Bt (curT E thr0 D Bt c x) ∣ e ∧
        ∃ Q' : Finset ι, (∀ z ∈ Q', ∃ j, z ∈ startPools E thr0 D Lv Bt (forceS ωs c) x
            (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c x).pools (curT E thr0 D Bt c x) j) ∧
          ∃ y : ι → Bool, c ∈ Q' ∧ c ∉ Fof Q' y ∧
            Covered E (fChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c) e θ (Fof Q' y) c R := by
  obtain ⟨hev, hret⟩ := outZ_cov h
  obtain ⟨hae, heT, hmin, x, hxe, -, hxs, hxn, -⟩ := remT_spec hD hLv hlev hthr hent hev
  subst hxe
  obtain ⟨hdvd, Q', hQ', y, h1, h2, h3⟩ := covered_of_removed_tpools hD hLv hlev hxs hxn
  refine ⟨hae, heT, ?_, ?_, x, rfl, hdvd, Q', ?_, y, h1, h2, h3⟩
  · intro y' h1' h2' hy'
    have hr : ∃ e0, retT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e0 := by
      classical
      unfold retT
      rw [dif_pos ⟨y', h1', by omega, hy'⟩]
      exact ⟨_, rfl⟩
    obtain ⟨e0, he0⟩ := hr
    have hlt := hret e0 he0
    obtain ⟨-, -, -, hnot⟩ := retT_spec he0
    exact hnot y' h1' (by omega) hy'
  · intro y' h1' h2'
    have := hmin y' h1' h2'
    rw [fRun_pools]; exact this
  · intro z hz
    rw [fRun_pools]; exact hQ' z hz

/-- **Certificate of a (b″) outcome.** The forced copy is retired at `e`, not before, and alive on `(E c, e)`. -/
theorem bev_certZ (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι}
    (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c) {e j : ℕ}
    (h : outZ E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c = .bev e j) :
    E c < e ∧ e ≤ T ∧ j = min (curT E thr0 D Bt c e) jmax ∧
      c ∈ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c e).aux ∧
      (∀ y, E c < y → y < e → c ∉ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c y).aux) ∧
      (∀ y, E c < y → y < e → ∃ r ℓ, c ∈ (fRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c y).pools r ℓ) := by
  obtain ⟨hev, hj, hrem⟩ := outZ_bev h
  obtain ⟨hae, heT, hin, hnot⟩ := retT_spec hev
  refine ⟨hae, heT, hj, hin, hnot, ?_⟩
  intro y h1 h2
  classical
  by_contra hna
  have hr : ∃ e', remT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e' := by
    unfold remT
    rw [dif_pos ⟨y, h1, by omega, hna⟩]
    exact ⟨_, rfl⟩
  obtain ⟨e', he'⟩ := hr
  have hle := hrem e' he'
  obtain ⟨-, -, hmin, -⟩ := remT_spec hD hLv hlev hthr hent he'
  have := hmin y h1 (by
    unfold remT at he'
    split_ifs at he' with hh
    simp only [Option.some.injEq] at he'
    have := Nat.find_min' hh ⟨h1, by omega, hna⟩
    omega)
  obtain ⟨r, ℓ, hc⟩ := this
  exact hna ⟨r, ℓ, by rw [fRun_pools]; exact hc⟩

end Certificates


section ZRule

variable {s : ℕ} {L : ℕ → ι → ℝ} {occ : Finset ι → Fin s → Option ι} {y : ℕ → Fin s}
  {rh : ℕ → ι → (ℕ → ℝ) → Bool}

/-- In the retirement process a copy retires only as a start-pool member, so not before its entry. -/
lemma E_lt_of_mem_aux (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) {c : ι} :
    ∀ a, c ∈ (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).aux → E c < a
  | 0, h => by simp [zRun, gRun] at h
  | a + 1, h => by
    rcases (mem_aux_succ E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a c).1 h with h1 | ⟨h1, -⟩
    · have := E_lt_of_mem_aux hD hLv hlev ωs φ a h1; omega
    · simp only [members, Finset.mem_biUnion, Finset.mem_range] at h1
      obtain ⟨r, -, ℓ, -, hc⟩ := h1
      have hok : BdOK E thr0 D Lv Bt a (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a).pools := by
        rw [gRun_pools_eq]
        exact tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (θ := θ) (R := R) (lev := lev) hD hLv hlev ωs φ a
      have hS := start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv hok ωs (x := a)
      have := (hS c r ℓ hc).1
      omega

/-- **(b″) outcome of the retirement process: the rule fired.** If the forced copy's outcome is `bev e j`, then at
unit `e - 1` it was a start-pool member of the forced run and the rule `rh` fired on its own data history
(e.g. "slot estimate since entry minus BASE's estimate ≥ Λ"). -/
theorem rule_of_bevZ (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {jmax T : ℕ}
    {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c)
    {e j : ℕ}
    (h : outZ E thr0 θ R K D Lv Bt lev (zUpd D Lv s L occ y rh) ∅ jmax T ωs φ c = .bev e j) :
    ∃ a, a + 1 = e ∧
      c ∈ members D Lv (startPools E thr0 D Lv Bt (forceS ωs c) a
        (zRun E thr0 θ R K D Lv Bt lev s L occ y rh (forceS ωs c) (forceF K φ c) a).pools) ∧
      rh a c ((zRun E thr0 θ R K D Lv Bt lev s L occ y rh (forceS ωs c) (forceF K φ c) (a + 1)).est c) = true := by
  obtain ⟨hae, -, -, hin, hnot, -⟩ := bev_certZ hD hLv hlev hthr hent h
  obtain ⟨a, rfl⟩ : ∃ a, e = a + 1 := ⟨e - 1, by omega⟩
  refine ⟨a, rfl, ?_⟩
  rcases (mem_aux_succ E thr0 θ R K D Lv Bt lev s L occ y rh (forceS ωs c) (forceF K φ c) a c).1 hin with h1 | h1
  · exfalso
    have hlt := E_lt_of_mem_aux hD hLv hlev (forceS ωs c) (forceF K φ c) a h1
    exact hnot a hlt (by omega) h1
  · exact h1

end ZRule

end Pool.P0168
