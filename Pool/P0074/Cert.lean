import Pool.P0065.Threads
import Pool.P0061.Chain

/-!
# Certificates for the threaded process: a dropped forced copy is chain-covered by actual copies present
# since their entry (the thread analogue of P0061)
-/

namespace Pool.P0074

open Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {C : ι → ℕ → ℝ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

/-- A start-pool member at unit `u + 1` that entered by `u` was in the pools at the boundary `u + 1`. -/
lemma mem_tpools_of_start (hD : 0 < D) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {u r ℓ : ℕ} {f : ι}
    (hf : f ∈ startPools E thr0 D Lv Bt ωs (u + 1) (tpools E thr0 C θ R K D Lv Bt lev ωs φ (u + 1)) r ℓ)
    (hE : E f ≤ u) : ∃ r' ℓ', f ∈ tpools E thr0 C θ R K D Lv Bt lev ωs φ (u + 1) r' ℓ' := by
  by_contra hne
  push Not at hne
  exact not_mem_startPools_of_not_alive hD hne (show E f ≠ u + 1 by omega) r ℓ hf

/-- A member of the pools at the boundary `u + 1` was in the start pools of unit `u`. -/
lemma mem_start_of_tpools {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {u r ℓ : ℕ} {f : ι}
    (hf : f ∈ tpools E thr0 C θ R K D Lv Bt lev ωs φ (u + 1) r ℓ) :
    ∃ ℓ', f ∈ startPools E thr0 D Lv Bt ωs u (tpools E thr0 C θ R K D Lv Bt lev ωs φ u) r ℓ' := by
  simp only [tpools] at hf
  split_ifs at hf
  · exact (mem_mergeUpTo _ _ ℓ f hf).1
  · exact ⟨ℓ, hf⟩

/-- **Presence back to entry.** A copy in the start pools of unit `x` was in the start pools of every
unit `u ∈ [E f, x]`. -/
lemma present_back (hD : 0 < D) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {f : ι} :
    ∀ (d x u : ℕ), x = u + d → E f ≤ u →
      (∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x) r ℓ) →
      ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u (tpools E thr0 C θ R K D Lv Bt lev ωs φ u) r ℓ
  | 0, x, u, hx, _, h => by subst hx; simpa using h
  | d + 1, x, u, hx, hE, ⟨r, ℓ, h⟩ => by
    subst hx
    have h1 := mem_tpools_of_start hD (u := u + d) (by rw [show u + (d + 1) = u + d + 1 by ring] at h; exact h)
      (by omega)
    obtain ⟨r', ℓ', h2⟩ := h1
    obtain ⟨ℓ'', h3⟩ := mem_start_of_tpools h2
    exact present_back hD d (u + d) u rfl hE ⟨r', ℓ'', h3⟩


/-- Piecewise version of P0061's `sum_le_pieceSum`: if on every interval `[s, s')` inside a chain
member's presence the learner is within `α + β (s' - s)` of that member, then on `[a, t)` the
learner is within `(#pieces)·α + β (t - a)` of the chain. -/
theorem sum_le_pieceSum_interval (cu : ℕ → ι → ℝ) (A : ℕ → ℝ) (α β : ℝ) (hβ : 0 ≤ β) (t : ℕ) :
    ∀ (ch : List ι) (a : ℕ), Pool.P0030.ChainOK E t ch a →
      (∀ f ∈ ch, ∀ s s', E f ≤ s → s ≤ s' → s' ≤ t →
        ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ)) →
      ∑ u ∈ Finset.Ico a t, A u ≤
        Pool.P0030.pieceSum E (Pool.P0061.cumL cu) t ch a + ch.length * α + β * ((t - a : ℕ) : ℝ)
  | [], a, hok, _ => hok.elim
  | [f], a, hok, hpres => by
    obtain ⟨hfa, hat⟩ := hok
    simp only [Pool.P0030.pieceSum, List.length_singleton, Nat.cast_one, one_mul]
    rw [Pool.P0061.Lint_cumL cu f hat]
    exact hpres f (by simp) a t hfa hat le_rfl
  | f :: g :: rest, a, hok, hpres => by
    obtain ⟨hfa, hag, hok'⟩ := hok
    have hgt : E g ≤ t := Pool.P0041.chain_le_t E t (g :: rest) (E g) hok'
    have ih := sum_le_pieceSum_interval cu A α β hβ t (g :: rest) (E g) hok'
      (fun f' hf' => hpres f' (List.mem_cons_of_mem _ hf'))
    have h1 := hpres f (by simp) a (E g) hfa hag hgt
    simp only [Pool.P0030.pieceSum, List.length_cons]
    rw [Pool.P0061.Lint_cumL cu f hag, ← Finset.sum_Ico_consecutive _ hag hgt]
    have hcast : ((t - a : ℕ) : ℝ) = ((E g - a : ℕ) : ℝ) + ((t - E g : ℕ) : ℝ) := by
      rw [← Nat.cast_add]; congr 1; omega
    simp only [List.length_cons] at ih
    push_cast at ih ⊢
    rw [hcast]
    nlinarith [ih, h1]

/-- **Certificate for the threaded process.** Let `c` be a copy that is not actually sampled
(`ωs c = false`). In the run where it is forced in as a never-filter copy, suppose it is in the start
pools of unit `x ≥ E c` and in no pool at the boundary `x + 1`. Then in the ACTUAL run, any learner
whose loss on each unit `u` is within `Rh` of every copy present in the start pools of `u` loses on
`[E c, x + 1)` at most `c`'s loss plus `θ + (x + 1 - E c)·Rh`. The cover data are the cumulative
unit losses `cumL cu` (K-query: exact losses). -/
theorem thread_cert (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cu : ℕ → ι → ℝ) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} (hc : ωs c = false)
    {x : ℕ} (hx : E c ≤ x)
    (hin : SAlive E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) x c)
    (hout : ¬ Alive E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c)
      (x + 1) c)
    (A : ℕ → ℝ) (Rh : ℝ)
    (hA : ∀ u f, (∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) → A u ≤ cu u f + Rh) :
    ∑ u ∈ Finset.Ico (E c) (x + 1), A u ≤
      ∑ u ∈ Finset.Ico (E c) (x + 1), cu u c + θ + ((x + 1 - E c : ℕ) : ℝ) * Rh := by
  classical
  set ωF := forceS ωs c
  set φF := forceF K φ c
  set CC := Pool.P0061.cumL cu
  obtain ⟨r0, ℓ0, h0⟩ := hin
  have hS := start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv
    (tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := CC) (θ := θ) (R := R) (lev := lev)
      hD hLv hlev ωF φF x) ωF (x := x)
  obtain ⟨-, hr0, -, -⟩ := hS c r0 ℓ0 h0
  -- the thread of `c` merges at `x + 1`
  have hdvd : Bt r0 ∣ x + 1 := by
    by_contra hnd
    apply hout
    refine ⟨r0, ℓ0, ?_⟩
    simp only [tpools]
    rw [if_neg hnd]; exact h0
  have hrem : ∀ j, c ∉ mergeUpTo E CC θ R K (φF r0) x (lev r0 x)
      (startPools E thr0 D Lv Bt ωF x (tpools E thr0 CC θ R K D Lv Bt lev ωF φF x) r0) j := by
    intro j hj
    apply hout
    refine ⟨r0, j, ?_⟩
    simp only [tpools]
    rw [if_pos hdvd]; exact hj
  obtain ⟨Q', hQ', y, hcQ, hcF, hcov⟩ := covered_of_removed_mergeUpTo (lev r0 x) _ ⟨ℓ0, h0⟩ hrem
  obtain ⟨ch, -, hchF, hok, hle⟩ := hcov
  -- chain members are actual copies present since their entry
  have hpres : ∀ f ∈ ch, ∀ u, E f ≤ u → u < x + 1 → A u ≤ cu u f + Rh := by
    intro f hf u hu1 hu2
    have hfF := hchF f hf
    have hfQ : f ∈ Q' := (Finset.mem_filter.1 hfF).1
    have hfc : f ≠ c := fun h => hcF (h ▸ hfF)
    obtain ⟨j, hj⟩ := hQ' f hfQ
    have hact : f ∈ startPools E thr0 D Lv Bt ωs x (tpools E thr0 CC θ R K D Lv Bt lev ωs φ x) r0 j := by
      rw [← forced_erase_start hc φ x r0 j]
      exact Finset.mem_erase.2 ⟨hfc, hj⟩
    have hEf : E f ≤ x := (start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv
      (tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := CC) (θ := θ) (R := R) (lev := lev)
        hD hLv hlev ωs φ x) ωs (x := x) f r0 j hact).1
    obtain ⟨r', ℓ', hu⟩ := present_back hD (x - u) x u (by omega) hu1 ⟨r0, j, hact⟩
    exact hA u f ⟨r', ℓ', hu⟩
  have key := Pool.P0061.sum_le_pieceSum E cu A Rh (x + 1) ch (E c) hok hpres
  rw [Pool.P0061.Lint_cumL cu c (by omega)] at hle
  linarith


/-- What an eviction time means: the forced copy is present at the start of unit `e - 1 ≥ a` and absent
at `e`. -/
theorem evict_spec (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {j a e : ℕ} (hj : j < D) (hd : Bt j ∣ a)
    (he : evict E thr0 C θ R K D Lv Bt lev T cstar ωs φ j a = some e) :
    E (cstar j a) = a ∧ ∃ x, a ≤ x ∧ x + 1 = e ∧ e ≤ T ∧
      SAlive E thr0 C θ R K D Lv Bt lev (forceS ωs (cstar j a)) (forceF K φ (cstar j a)) x (cstar j a) ∧
      ¬ Alive E thr0 C θ R K D Lv Bt lev (forceS ωs (cstar j a)) (forceF K φ (cstar j a)) (x + 1)
        (cstar j a) := by
  classical
  have hD := hB.hD
  set c := cstar j a with hc
  unfold evict at he
  split_ifs at he with h
  simp only [Option.some.injEq] at he
  obtain ⟨hae, heT, hna⟩ := he ▸ Nat.find_spec h
  have hE' := hE j a (by omega) hd (by omega)
  have hthr' := hthr j a (by omega) hd (by omega)
  have hmin : ∀ y, a < y → y < e → Alive E thr0 C θ R K D Lv Bt lev (forceS ωs c)
      (forceF K φ c) y c := by
    intro y h1 h2
    by_contra hc'
    exact Nat.find_min h (he ▸ h2) ⟨h1, by omega, hc'⟩
  have hs0 : SAlive E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) a c := by
    have := salive_entry (E := E) (thr0 := thr0) (D := D) (Lv := Lv) (Bt := Bt) (K := K)
      (C := C) (θ := θ) (R := R) (lev := lev) (φ := forceF K φ c) hD hLv
      (c := c) (ωs := forceS ωs c) (by simp [forceS])
      (by rw [hc, hthr']; omega) (by rw [hc, hthr', hE']; exact hd)
    rwa [hc, hE'] at this
  obtain ⟨x, hx1, hx2, hx3, hx4, -⟩ := removal_dvd hD hLv hlev hs0 e hae hna
  have hxe : x + 1 = e := by
    by_contra hne
    exact hx4 (hmin (x + 1) (by omega) (by omega))
  exact ⟨hE', x, hx1, hxe, heT, hx3, hx4⟩

/-- **Certificate at an eviction time** (input of the walk's good intervals). If the comparator's copy
`cstar j a` is not actually sampled and `evict … j a = some e`, any learner within `Rh` of the start
pools on each unit loses on `[a, e)` at most the copy's loss plus `θ + (e - a)·Rh`. -/
theorem evict_cert (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}
    {j a e : ℕ} (hj : j < D) (hd : Bt j ∣ a) (hc : ωs (cstar j a) = false)
    (he : evict E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev T cstar ωs φ j a = some e)
    (A : ℕ → ℝ) (Rh : ℝ)
    (hA : ∀ u f, (∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) → A u ≤ cu u f + Rh) :
    ∑ u ∈ Finset.Ico a e, A u ≤ ∑ u ∈ Finset.Ico a e, cu u (cstar j a) + θ + ((e - a : ℕ) : ℝ) * Rh := by
  obtain ⟨hE', x, hax, hxe, -, hin, hout⟩ := evict_spec hB hLv hlev cstar hE hthr hj hd he
  have := thread_cert hB.hD hLv hlev cu hc (x := x) (by rw [hE']; exact hax) hin hout A Rh hA
  rw [hE', hxe] at this
  exact this


/-- **Interval-regret form of the thread certificate** (for boosting): if the learner is within
`α + β·len` of every copy on every interval during which that copy is present in the start pools, then
on `[E c, x + 1)` it loses at most the dropped copy's loss plus `θ + R·α + β·(x + 1 - E c)`. -/
theorem thread_cert_interval (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cu : ℕ → ι → ℝ) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} (hc : ωs c = false)
    {x : ℕ} (hx : E c ≤ x)
    (hin : SAlive E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) x c)
    (hout : ¬ Alive E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c)
      (x + 1) c)
    (A : ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ)) :
    ∑ u ∈ Finset.Ico (E c) (x + 1), A u ≤
      ∑ u ∈ Finset.Ico (E c) (x + 1), cu u c + θ + R * α + β * ((x + 1 - E c : ℕ) : ℝ) := by
  classical
  set ωF := forceS ωs c
  set φF := forceF K φ c
  set CC := Pool.P0061.cumL cu
  obtain ⟨r0, ℓ0, h0⟩ := hin
  have hS := start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv
    (tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := CC) (θ := θ) (R := R) (lev := lev)
      hD hLv hlev ωF φF x) ωF (x := x)
  obtain ⟨-, hr0, -, -⟩ := hS c r0 ℓ0 h0
  have hdvd : Bt r0 ∣ x + 1 := by
    by_contra hnd
    apply hout
    refine ⟨r0, ℓ0, ?_⟩
    simp only [tpools]
    rw [if_neg hnd]; exact h0
  have hrem : ∀ j, c ∉ mergeUpTo E CC θ R K (φF r0) x (lev r0 x)
      (startPools E thr0 D Lv Bt ωF x (tpools E thr0 CC θ R K D Lv Bt lev ωF φF x) r0) j := by
    intro j hj
    apply hout
    refine ⟨r0, j, ?_⟩
    simp only [tpools]
    rw [if_pos hdvd]; exact hj
  obtain ⟨Q', hQ', y, hcQ, hcF, hcov⟩ := covered_of_removed_mergeUpTo (lev r0 x) _ ⟨ℓ0, h0⟩ hrem
  obtain ⟨ch, hlen, hchF, hok, hle⟩ := hcov
  have hpres : ∀ f ∈ ch, ∀ s s', E f ≤ s → s ≤ s' → s' ≤ x + 1 →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ) := by
    intro f hf s s' hs hss' hs'
    have hfF := hchF f hf
    have hfQ : f ∈ Q' := (Finset.mem_filter.1 hfF).1
    have hfc : f ≠ c := fun h => hcF (h ▸ hfF)
    obtain ⟨j, hj⟩ := hQ' f hfQ
    have hact : f ∈ startPools E thr0 D Lv Bt ωs x (tpools E thr0 CC θ R K D Lv Bt lev ωs φ x) r0 j := by
      rw [← forced_erase_start hc φ x r0 j]
      exact Finset.mem_erase.2 ⟨hfc, hj⟩
    refine hA f s s' hss' (fun u hu1 hu2 => ?_)
    exact present_back hD (x - u) x u (by omega) (by omega) ⟨r0, j, hact⟩
  have key := sum_le_pieceSum_interval (E := E) cu A α β hβ (x + 1) ch (E c) hok hpres
  rw [Pool.P0061.Lint_cumL cu c (by omega)] at hle
  have : (ch.length : ℝ) * α ≤ R * α := by
    apply mul_le_mul_of_nonneg_right _ hα; exact_mod_cast hlen
  linarith

/-- Interval-regret certificate at an eviction time of the comparator's forced copy. -/
theorem evict_cert_interval (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}
    {j a e : ℕ} (hj : j < D) (hd : Bt j ∣ a) (hc : ωs (cstar j a) = false)
    (he : evict E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev T cstar ωs φ j a = some e)
    (A : ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ)) :
    ∑ u ∈ Finset.Ico a e, A u ≤
      ∑ u ∈ Finset.Ico a e, cu u (cstar j a) + θ + R * α + β * ((e - a : ℕ) : ℝ) := by
  obtain ⟨hE', x, hax, hxe, -, hin, hout⟩ := evict_spec hB hLv hlev cstar hE hthr hj hd he
  have := thread_cert_interval hB.hD hLv hlev cu hc (x := x) (by rw [hE']; exact hax) hin hout
    A α β hα hβ hA
  rw [hE', hxe] at this
  exact this

end Pool.P0074
