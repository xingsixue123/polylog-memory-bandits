import Pool.P0086.WalkCount
import Pool.P0074.Cert

/-!
# The threaded pool process (P0065) over P0057's inheritance walk: walk data, certificates, and the
# per-run regret bound

* `cert_actual`: an actually present copy removed by a merge is chain-covered by copies present since
  their entry, so a learner within `α + β·len` of every present copy on every interval loses at most
  `θ + R·α + β·len` against it (the threaded analogue of P0071's `cert_actual`).
* `actEv`, **`evW`**: the walk data in P0071's style. On the grid, follow the actual copy of the
  comparator if it is sampled (its removal time, or `T` if it survives); otherwise follow the forced
  copy (P0065's `evict`, `none` = bad).
* `actEv_spec`, **`hyp_evW`**: `evW` satisfies P0057's `Hyp`.
* `chain_sum_Ico`, **`cert_evW`**: the certificate on every covered walk record.
* **`run_bound`**, **`run_bound_closed`**: per run,
  `Σ_{u<T} (A u - g u) ≤ (θ + R α)·(T/B 0 + Σ_{j<D-1} B j·H j/B (j+1)) + β T + Bep·B (D-1)·H (D-1)`,
  with `H = nBad` of `evW` (the number of bad walk points of each thread).

Scope. Everything is deterministic given the coins; there is no probability in this file. In
particular, NO bound on `H` (or on `E[H]`) is proved here: bounding the bad points by a P0048-style
counting argument is future work (CLAIMED, not formalized). The certificates use EXACT cumulative
losses (`C = cumL cu`, the K-query / full-observation setting): covers built from one-query or
estimated losses are not covered by these statements.
-/

namespace Pool.P0086

open Pool.P0065 Pool.P0074 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

/-- **Certificate for an actually present copy removed by a merge.** If `c` is in the start pools of
unit `x` and in no pool at `x + 1` (in the actual run), then a learner within `α + β·len` of every
present copy on every interval loses on `[E c, x + 1)` at most `c`'s loss plus `θ + R·α + β·(x+1-E c)`. -/
theorem cert_actual (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cu : ℕ → ι → ℝ) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι}
    {x : ℕ} (hx : E c ≤ x)
    (hin : SAlive E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ x c)
    (hout : ¬ Alive E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ (x + 1) c)
    (A : ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ)) :
    ∑ u ∈ Finset.Ico (E c) (x + 1), A u ≤
      ∑ u ∈ Finset.Ico (E c) (x + 1), cu u c + θ + R * α + β * ((x + 1 - E c : ℕ) : ℝ) := by
  classical
  set CC := Pool.P0061.cumL cu
  obtain ⟨r0, ℓ0, h0⟩ := hin
  have hdvd : Bt r0 ∣ x + 1 := by
    by_contra hnd
    apply hout
    refine ⟨r0, ℓ0, ?_⟩
    simp only [tpools]
    rw [if_neg hnd]; exact h0
  have hrem : ∀ j, c ∉ mergeUpTo E CC θ R K (φ r0) x (lev r0 x)
      (startPools E thr0 D Lv Bt ωs x (tpools E thr0 CC θ R K D Lv Bt lev ωs φ x) r0) j := by
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
    obtain ⟨j, hj⟩ := hQ' f hfQ
    refine hA f s s' hss' (fun u hu1 hu2 => ?_)
    exact present_back hD (x - u) x u (by omega) (by omega) ⟨r0, j, hj⟩
  have key := sum_le_pieceSum_interval (E := E) cu A α β hβ (x + 1) ch (E c) hok hpres
  rw [Pool.P0061.Lint_cumL cu c (by omega)] at hle
  have : (ch.length : ℝ) * α ≤ R * α := by
    apply mul_le_mul_of_nonneg_right _ hα; exact_mod_cast hlen
  linarith


section Walk

variable {C : ι → ℕ → ℝ}

open Classical in
/-- Eviction time of a copy `c` that is actually present from unit `a` on: the first boundary in
`(a, T]` where it is in no pool, or `T` if it survives. -/
noncomputable def actEv (E thr0 : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
    (lev : ℕ → ℕ → ℕ) (T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) (a : ℕ) : ℕ :=
  if h : ∃ y, a < y ∧ y ≤ T ∧ ¬ Alive E thr0 C θ R K D Lv Bt lev ωs φ y c then Nat.find h else T

open Classical in
/-- **The walk data of the threaded process** (P0057 indexing `t τ r`): on the grid, follow the actual
copy `cstar r τ` if it is sampled (its removal time, or `T`), and the forced copy otherwise (P0065's
`evict`, `none` = bad epoch). -/
noncomputable def evW (E thr0 : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
    (lev : ℕ → ℕ → ℕ) (T : ℕ) (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (τ r : ℕ) : Option ℕ :=
  if r < D ∧ Bt r ∣ τ ∧ τ < T then
    (if ωs (cstar r τ) = true then some (actEv E thr0 C θ R K D Lv Bt lev T ωs φ (cstar r τ) τ)
     else evict E thr0 C θ R K D Lv Bt lev T cstar ωs φ r τ)
  else none

/-- Facts about `actEv` for a sampled copy: removal time with the walk divisibility properties. -/
lemma actEv_spec (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι}
    (hs : ωs c = true) (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c) (hET : E c < T) :
    Bt (thr0 c) ∣ actEv E thr0 C θ R K D Lv Bt lev T ωs φ c (E c) ∧
      E c + Bt (thr0 c) ≤ actEv E thr0 C θ R K D Lv Bt lev T ωs φ c (E c) ∧
      actEv E thr0 C θ R K D Lv Bt lev T ωs φ c (E c) ≤ T ∧
      (∀ i m, i < thr0 c → Bt i ∣ m → E c < m → m < actEv E thr0 C θ R K D Lv Bt lev T ωs φ c (E c) →
        Bt i ∣ actEv E thr0 C θ R K D Lv Bt lev T ωs φ c (E c)) := by
  classical
  have hD := hB.hD
  have hTd : ∀ i, i < D → Bt i ∣ T := fun i hi => (hB.dvd_of_le (Nat.zero_le i) hi).trans hT
  -- the survival case
  have hsurv : Bt (thr0 c) ∣ T ∧ E c + Bt (thr0 c) ≤ T ∧ T ≤ T ∧
      (∀ i m, i < thr0 c → Bt i ∣ m → E c < m → m < T → Bt i ∣ T) := by
    refine ⟨hTd _ hthr, ?_, le_rfl, fun i m hi _ _ _ => hTd i (by omega)⟩
    obtain ⟨k, hk⟩ := hent
    obtain ⟨m, hm⟩ := hTd _ hthr
    have hp := hB.pos (thr0 c)
    have : k < m := by
      by_contra hc; push Not at hc
      have : Bt (thr0 c) * m ≤ Bt (thr0 c) * k := Nat.mul_le_mul_left _ hc
      omega
    calc E c + Bt (thr0 c) = Bt (thr0 c) * (k + 1) := by rw [hk]; ring
      _ ≤ Bt (thr0 c) * m := Nat.mul_le_mul_left _ this
      _ = T := hm.symm
  unfold actEv
  split_ifs with h
  · obtain ⟨hae, heT, hna⟩ := Nat.find_spec h
    have hmin : ∀ y, E c < y → y < Nat.find h → Alive E thr0 C θ R K D Lv Bt lev ωs φ y c := by
      intro y h1 h2
      by_contra hc'
      exact Nat.find_min h h2 ⟨h1, by omega, hc'⟩
    have hs0 := salive_entry (E := E) (thr0 := thr0) (D := D) (Lv := Lv) (Bt := Bt) (K := K)
      (C := C) (θ := θ) (R := R) (lev := lev) (φ := φ) hD hLv hs hthr hent
    obtain ⟨x, hx1, hx2, -, hx4, hx5⟩ := removal_dvd hD hLv hlev hs0 _ hae hna
    have hxe : x + 1 = Nat.find h := by
      by_contra hne
      exact hx4 (hmin (x + 1) (by omega) (by omega))
    have := removal_hyp (E := E) (thr0 := thr0) (D := D) (Bt := Bt) hB hthr hent (x := x) hx1 hx5
    rw [← hxe]
    exact ⟨this.1, this.2.1, by omega, this.2.2⟩
  · exact hsurv

/-- **`evW` satisfies P0057's walk hypotheses.** -/
theorem hyp_evW (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    Pool.P0057.Hyp D T Bt (evW E thr0 C θ R K D Lv Bt lev T cstar ωs φ) := by
  classical
  have hD := hB.hD
  -- the facts for every covered grid point
  have key : ∀ τ r e, Bt r ∣ τ → τ < T → r < D →
      evW E thr0 C θ R K D Lv Bt lev T cstar ωs φ τ r = some e →
      Bt r ∣ e ∧ τ + Bt r ≤ e ∧ e ≤ T ∧ ∀ i m, i < r → Bt i ∣ m → τ < m → m < e → Bt i ∣ e := by
    intro τ r e hd hτ hr he
    unfold evW at he
    rw [if_pos ⟨hr, hd, hτ⟩] at he
    have hE' := hE r τ (by omega) hd hτ
    have hthr' := hthr r τ (by omega) hd hτ
    split_ifs at he with hs
    · simp only [Option.some.injEq] at he
      subst he
      have := actEv_spec (E := E) (thr0 := thr0) (C := C) (θ := θ) (R := R) (lev := lev) (φ := φ)
        hB hLv hlev hT hs
        (by rw [hthr']; exact hr) (by rw [hthr', hE']; exact hd) (by rw [hE']; exact hτ)
      rw [hthr', hE'] at this
      exact this
    · exact Pool.P0065.hypI_evict.key (E := E) (thr0 := thr0) (C := C) (θ := θ) (R := R) (lev := lev)
        hB hLv hlev cstar hE hthr ωs φ r τ e (by omega) hd hτ he
  exact {
    pos := hB.pos
    dvd := hB.dvd
    hR := hD
    hT := hT
    lb := fun τ r e hd hτ hr he => (key τ r e hd hτ hr he).2.1
    ub := fun τ r e hd hτ hr he => (key τ r e hd hτ hr he).2.2.1
    edvd := fun τ r e hd hτ hr he => (key τ r e hd hτ hr he).1
    align := fun τ r e hd hτ hr he j m hj hm h1 h2 => (key τ r e hd hτ hr he).2.2.2 j m hj hm h1 h2 }

end Walk


section Run

variable {C : ι → ℕ → ℝ}

/-- Sums over `[τ, T)` split along a chain of consecutive records. -/
lemma chain_sum_Ico {T : ℕ} (f : ℕ → ℝ) : ∀ (L : List Pool.P0057.Rec) (τ : ℕ), Pool.P0057.Chain T τ L →
    ∑ u ∈ Finset.Ico τ T, f u = (L.map fun x => ∑ u ∈ Finset.Ico x.start x.stop, f u).sum
  | [], τ, hc => by simp [Pool.P0057.Chain] at hc; simp [hc]
  | x :: L, τ, ⟨hs, hlt, hc⟩ => by
    have ih := chain_sum_Ico f L x.stop hc
    have hle : x.stop ≤ T := by
      clear ih hs hlt
      induction L generalizing x with
      | nil => exact le_of_eq hc
      | cons y L' ihL => exact (le_of_lt hc.2.1).trans (ihL y hc.2.2)
    rw [List.map_cons, List.sum_cons, ← ih, ← hs,
      Finset.sum_Ico_consecutive _ (by omega) hle]

end Run


section Cert

/-- **Certificate for every covered walk point** of `evW`. -/
theorem cert_evW (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (A : ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ))
    {τ r e : ℕ} (hd : Bt r ∣ τ) (hτ : τ < T) (hr : r < D)
    (he : evW E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev T cstar ωs φ τ r = some e) :
    ∑ u ∈ Finset.Ico τ e, A u ≤
      ∑ u ∈ Finset.Ico τ e, cu u (cstar r τ) + θ + R * α + β * ((e - τ : ℕ) : ℝ) := by
  classical
  have hD := hB.hD
  have hE' := hE r τ (by omega) hd hτ
  have hthr' := hthr r τ (by omega) hd hτ
  set c := cstar r τ with hc
  set CC := Pool.P0061.cumL cu
  have hRα : α ≤ R * α := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR1
    nlinarith
  unfold evW at he
  rw [if_pos ⟨hr, hd, hτ⟩] at he
  split_ifs at he with hs
  · simp only [Option.some.injEq] at he
    have hs0 := salive_entry (E := E) (thr0 := thr0) (D := D) (Lv := Lv) (Bt := Bt) (K := K)
      (C := CC) (θ := θ) (R := R) (lev := lev) (φ := φ) hD hLv (c := c) hs
      (by rw [hthr']; exact hr) (by rw [hthr', hE']; exact hd)
    rw [hE'] at hs0
    unfold actEv at he
    split_ifs at he with h
    · -- removed at `Nat.find h`
      obtain ⟨hae, heT, hna⟩ := Nat.find_spec h
      have hmin : ∀ y, τ < y → y < Nat.find h → Alive E thr0 CC θ R K D Lv Bt lev ωs φ y c := by
        intro y h1 h2
        by_contra hc'
        exact Nat.find_min h h2 ⟨h1, by omega, hc'⟩
      obtain ⟨x, hx1, hx2, hx3, hx4, -⟩ := removal_dvd hD hLv hlev hs0 _ hae hna
      have hxe : x + 1 = Nat.find h := by
        by_contra hne
        exact hx4 (hmin (x + 1) (by omega) (by omega))
      have := cert_actual hD hLv hlev cu (c := c) (x := x) (by rw [hE']; exact hx1) hx3 hx4
        A α β hα hβ hA
      rw [hE', hxe, he] at this
      exact this
    · -- survives to `T`
      subst he
      have hpres : ∀ u, τ ≤ u → u < T → ∃ r' ℓ', c ∈ startPools E thr0 D Lv Bt ωs u
          (tpools E thr0 CC θ R K D Lv Bt lev ωs φ u) r' ℓ' := by
        intro u hu1 hu2
        rcases hu1.lt_or_eq with hu | rfl
        · have hal : Alive E thr0 CC θ R K D Lv Bt lev ωs φ u c := by
            by_contra hna; exact h ⟨u, hu, hu2.le, hna⟩
          exact salive_of_alive hD hLv hlev hal
        · exact hs0
      have := hA c τ T hτ.le hpres
      linarith
  · exact evict_cert_interval hB hLv hlev cu cstar hE hthr hr hd (by simpa using hs) he A α β hα hβ hA

end Cert


section RunBound

/-- **Per-run regret bound of the threaded process over the walk** (deterministic). For a learner `A`
within `α + β·len` of every present copy on every interval and within `Bep` of the comparator on each
unit, the regret against the comparator (unit losses `g`, shared by all its copies `cstar j a`) is at
most `(θ + R·α)·#records + β·T + Bep·Σ_{bad finest records} len`. -/
theorem run_bound (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < T → cu u (cstar j a) = g u)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (A : ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ))
    (hBep : ∀ u, A u - g u ≤ Bep) :
    let W := Pool.P0057.theWalk D T Bt (evW E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev T cstar ωs φ)
    ∑ u ∈ Finset.range T, (A u - g u) ≤ (θ + R * α) * W.length + β * T +
      Bep * (((W.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) := by
  intro W
  have hH := hyp_evW (C := Pool.P0061.cumL cu) (θ := θ) (R := R) (lev := lev) hB hLv hlev hT cstar hE hthr
    ωs φ
  obtain ⟨hc, hok, hsum, -⟩ := Pool.P0057.theWalk_spec hH
  rw [show Finset.range T = Finset.Ico 0 T from Finset.range_eq_Ico T]
  rw [chain_sum_Ico (fun u => A u - g u) W 0 hc]
  -- pointwise bound per record
  have hrec : ∀ x ∈ W, ∑ u ∈ Finset.Ico x.start x.stop, (A u - g u) ≤
      (θ + R * α) + β * (Pool.P0057.len x : ℝ) + (if x.cov then 0 else Bep * (Pool.P0057.len x : ℝ)) := by
    intro x hx
    have hx' := hok x hx
    cases hcv : x.cov
    · -- finest bad record
      simp only [Bool.false_eq_true, if_false]
      have h1 : ∑ u ∈ Finset.Ico x.start x.stop, (A u - g u) ≤ ∑ _u ∈ Finset.Ico x.start x.stop, Bep :=
        Finset.sum_le_sum fun u _ => hBep u
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
      have hlen : ((x.stop - x.start : ℕ) : ℝ) = (Pool.P0057.len x : ℝ) := rfl
      rw [hlen] at h1
      have h2 : (0 : ℝ) ≤ θ + R * α := by
        have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
        positivity
      have h3 : (0 : ℝ) ≤ β * (Pool.P0057.len x : ℝ) := by positivity
      linarith
    · simp only [if_true, add_zero]
      have hxT : x.start < T := lt_of_lt_of_le hx'.lt hx'.le
      have hcert := cert_evW (θ := θ) hB hLv hlev hT cu cstar hE hthr ωs φ A α β hα hβ hθ hR1 hA
        hx'.inv.dvd hxT hx'.inv.lt (hx'.cov hcv)
      have hgs : ∑ u ∈ Finset.Ico x.start x.stop, cu u (cstar x.lvl x.start) =
          ∑ u ∈ Finset.Ico x.start x.stop, g u :=
        Finset.sum_congr rfl fun u _ => hg x.lvl x.start u (by have := hx'.inv.lt; omega) hx'.inv.dvd hxT
      rw [hgs] at hcert
      rw [Finset.sum_sub_distrib]
      have hlen : ((x.stop - x.start : ℕ) : ℝ) = (Pool.P0057.len x : ℝ) := rfl
      rw [hlen] at hcert
      linarith
  calc (W.map fun x => ∑ u ∈ Finset.Ico x.start x.stop, (A u - g u)).sum
      ≤ (W.map fun x => (θ + R * α) + β * (Pool.P0057.len x : ℝ) +
          (if x.cov then 0 else Bep * (Pool.P0057.len x : ℝ))).sum := List.sum_le_sum hrec
    _ = (θ + R * α) * W.length + β * T + Bep * (((W.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) := by
        have key : ∀ (M : List Pool.P0057.Rec), (M.map fun x => (θ + R * α) + β * (Pool.P0057.len x : ℝ) +
            (if x.cov then 0 else Bep * (Pool.P0057.len x : ℝ))).sum =
            (θ + R * α) * M.length + β * ((M.map Pool.P0057.len).sum : ℕ) +
              Bep * (((M.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) := by
          intro M
          induction M with
          | nil => simp
          | cons y M ih =>
            rw [List.map_cons, List.sum_cons, ih]
            cases hy : y.cov <;> simp [hy, List.filter_cons] <;> push_cast <;> ring
        rw [key, hsum]

end RunBound


section Closed

/-- **Per-run regret bound in closed form**: with `H j` the number of bad walk points of thread `j`
(`nBad` of `evW`: the comparator's copy not sampled and, forced in, never evicted),
`Σ_u (A u - g u) ≤ (θ + R α)·(T/B 0 + Σ_{j<D-1} B j·H j/B (j+1)) + β T + Bep·B (D-1)·H (D-1)`.
This is a deterministic per-run bound with `H` left as is: no bound on `H` is proved here. The covers
use exact cumulative losses `cumL cu` (K-query setting), not one-query estimates. -/
theorem run_bound_closed (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < T → cu u (cstar j a) = g u)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (A : ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ))
    (hBep : ∀ u, A u - g u ≤ Bep) :
    let H := Pool.P0057.nBad T Bt (evW E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev T cstar ωs φ)
    ∑ u ∈ Finset.range T, (A u - g u) ≤
      (θ + R * α) * (T / Bt 0 + ∑ j ∈ Finset.range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1)) +
        β * T + Bep * (Bt (D - 1) * H (D - 1) : ℕ) := by
  intro H
  have hH := hyp_evW (C := Pool.P0061.cumL cu) (θ := θ) (R := R) (lev := lev) hB hLv hlev hT cstar hE hthr
    ωs φ
  have h1 := run_bound (θ := θ) hB hLv hlev hT cu cstar hE hthr g hg ωs φ A α β Bep hα hβ hθ hR1 hA hBep
  have h2 := card_walk_le hH
  have h3 := sum_bad_len_le hH
  have hc0 : (0 : ℝ) ≤ θ + R * α := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    positivity
  refine h1.trans ?_
  gcongr

end Closed

end Pool.P0086
