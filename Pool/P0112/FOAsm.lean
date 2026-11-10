import Pool.P0105.FOConc
import Pool.P0086.Asm

/-!
# The one-free-observation threaded process over the inheritance walk: per-run regret bound

P0086's walk assembly for the K-query process, redone for P0095's one-free-observation process. Each forced
copy lives in its OWN forced copy-last run, with its own realized estimates.

* `evWF`: P0086's walk data `evW` with per-point forced data. `hyp_evWF`: it satisfies P0057's `Hyp`; the proof is
  P0086's, pointwise in the data.
* `recData`, `evFO`: the FO instance. The actual run is entry order (`occSort`) with its realized estimates. The
  forced copy of `(r, τ)` is in the copy-last run with `forceS`/`forceF`.
* `cert_evFO`: on every covered record `[τ, e)`, the learner is within `θ + Rα + β·(e − τ)` of the record's data
  (P0086's `cert_actual` for sampled copies, P0105's `fo_cert` for forced ones).
* `run_bound_FO`: `Σ (A − g) ≤ (θ + Rα)·#records + βT + Bep·(bad length) + Σ_records z(len)`, when every covered
  record's data overestimate the comparator's true loss by at most `z(len)`.
* `run_bound_FO_closed`: the closed form for `z(len) = a√len + b`, by P0086's walk counts and P0057's `sum_sqrt_le`.

Everything is deterministic given all the coins. The estimation-error hypothesis `hz` is NOT proved here.
-/

namespace Pool.P0112

open Pool.P0065 Pool.P0074 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0095 Pool.P0105

section Walk

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

open Classical in
/-- **Walk data with per-point forced data.** On the grid, follow the actual copy `cstar r τ` if it is sampled
(actual run, data `CA`), and otherwise the forced copy in its OWN forced run (data `CF r τ`). This is P0086's `evW`
with the forced runs' cover data allowed to depend on the forced copy. -/
noncomputable def evWF (E thr0 : ι → ℕ) (CA : ι → ℕ → ℝ) (CF : ℕ → ℕ → ι → ℕ → ℝ) (θ : ℝ) (R K D Lv : ℕ)
    (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (T : ℕ) (cstar : ℕ → ℕ → ι) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (τ r : ℕ) : Option ℕ :=
  if r < D ∧ Bt r ∣ τ ∧ τ < T then
    (if ωs (cstar r τ) = true then some (Pool.P0086.actEv E thr0 CA θ R K D Lv Bt lev T ωs φ (cstar r τ) τ)
     else evict E thr0 (CF r τ) θ R K D Lv Bt lev T cstar ωs φ r τ)
  else none

/-- **`evWF` satisfies P0057's walk hypotheses** (P0086's `hyp_evW`, pointwise in the data). -/
theorem hyp_evWF (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (CA : ι → ℕ → ℝ) (CF : ℕ → ℕ → ι → ℕ → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    Pool.P0057.Hyp D T Bt (evWF E thr0 CA CF θ R K D Lv Bt lev T cstar ωs φ) := by
  classical
  have hD := hB.hD
  have key : ∀ τ r e, Bt r ∣ τ → τ < T → r < D →
      evWF E thr0 CA CF θ R K D Lv Bt lev T cstar ωs φ τ r = some e →
      Bt r ∣ e ∧ τ + Bt r ≤ e ∧ e ≤ T ∧ ∀ i m, i < r → Bt i ∣ m → τ < m → m < e → Bt i ∣ e := by
    intro τ r e hd hτ hr he
    unfold evWF at he
    rw [if_pos ⟨hr, hd, hτ⟩] at he
    have hE' := hE r τ (by omega) hd hτ
    have hthr' := hthr r τ (by omega) hd hτ
    split_ifs at he with hs
    · simp only [Option.some.injEq] at he
      subst he
      have := Pool.P0086.actEv_spec (E := E) (thr0 := thr0) (C := CA) (θ := θ) (R := R) (lev := lev) (φ := φ)
        hB hLv hlev hT hs
        (by rw [hthr']; exact hr) (by rw [hthr', hE']; exact hd) (by rw [hE']; exact hτ)
      rw [hthr', hE'] at this
      exact this
    · exact Pool.P0065.hypI_evict.key (E := E) (thr0 := thr0) (C := CF r τ) (θ := θ) (R := R) (lev := lev)
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

section FOCert

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

/-- The data of the record started at `(τ, r)`: the actual run's estimates of the comparator's copy if it is
sampled, and its own forced copy-last run's estimates otherwise. -/
noncomputable def recData (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ)
    (L : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s)
    (r τ : ℕ) : ℕ → ℝ :=
  if ωs (cstar r τ) = true then Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y (cstar r τ)
  else Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
    (forceF K φ (cstar r τ)) y (cstar r τ)

/-- The FO walk data: `evWF` with the actual run's estimates and each forced copy's own forced-run estimates. -/
noncomputable abbrev evFO (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ)
    (L : ℕ → ι → ℝ) (T : ℕ) (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (y : ℕ → Fin s) : ℕ → ℕ → Option ℕ :=
  evWF E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y)
    (fun r τ => Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
      (forceF K φ (cstar r τ)) y) θ R K D Lv Bt lev T cstar ωs φ

/-- **Certificate on every covered FO walk point.** If the learner is within `α + β·len` of the actual run's
realized estimates of every copy on every interval of its presence, then on every covered record `[τ, e)` it is
within `θ + Rα + β·(e − τ)` of the record's data (`recData`). -/
theorem cert_evFO (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (s : ℕ) (L : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s)
    (A : ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R)
    (hA : ∀ f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).pools r ℓ) →
      ∑ u ∈ Finset.Ico a b, A u ≤ Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f b -
        Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f a + α + β * ((b - a : ℕ) : ℝ))
    {τ r e : ℕ} (hd : Bt r ∣ τ) (hτ : τ < T) (hr : r < D)
    (he : evFO E thr0 θ R K D Lv Bt lev s L T cstar ωs φ y τ r = some e) :
    ∑ u ∈ Finset.Ico τ e, A u ≤
      recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ e -
        recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ τ + θ + R * α + β * ((e - τ : ℕ) : ℝ) := by
  classical
  have hD := hB.hD
  have hE' := hE r τ (by omega) hd hτ
  have hthr' := hthr r τ (by omega) hd hτ
  set c := cstar r τ with hc
  set CA := Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y with hCA
  have hCA0 : ∀ x, CA x 0 = 0 := fun _ => rfl
  have hcum : Pool.P0061.cumL (incrOf CA) = CA := cumL_incrOf CA hCA0
  -- the learner hypothesis in P0086's form
  have hA' : ∀ f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL (incrOf CA)) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico a b, A u ≤ ∑ u ∈ Finset.Ico a b, incrOf CA u f + α + β * ((b - a : ℕ) : ℝ) := by
    intro f a b hab hpres
    rw [sum_Ico_incrOf CA f hab]
    refine hA f a b hab fun u h1 h2 => ?_
    obtain ⟨r', ℓ', hm⟩ := hpres u h1 h2
    refine ⟨r', ℓ', ?_⟩
    rwa [hcum, hCA, ← foRun_pools_eq E thr0 θ R K D Lv Bt lev s L] at hm
  unfold evFO evWF at he
  rw [if_pos ⟨hr, hd, hτ⟩] at he
  unfold recData
  split_ifs at he ⊢ with hs
  · simp only [Option.some.injEq] at he
    rw [← hCA, ← hc, ← hcum] at he
    rw [← hCA, ← hc]
    have hs0 := salive_entry (E := E) (thr0 := thr0) (D := D) (Lv := Lv) (Bt := Bt) (K := K)
      (C := Pool.P0061.cumL (incrOf CA)) (θ := θ) (R := R) (lev := lev) (φ := φ) hD hLv (c := c) hs
      (by rw [hthr']; exact hr) (by rw [hthr', hE']; exact hd)
    rw [hE'] at hs0
    unfold Pool.P0086.actEv at he
    split_ifs at he with h
    · obtain ⟨hae, heT, hna⟩ := Nat.find_spec h
      have hmin : ∀ y', τ < y' → y' < Nat.find h →
          Alive E thr0 (Pool.P0061.cumL (incrOf CA)) θ R K D Lv Bt lev ωs φ y' c := by
        intro y' h1 h2
        by_contra hc'
        exact Nat.find_min h h2 ⟨h1, by omega, hc'⟩
      obtain ⟨x, hx1, hx2, hx3, hx4, -⟩ := removal_dvd hD hLv hlev hs0 _ hae hna
      have hxe : x + 1 = Nat.find h := by
        by_contra hne
        exact hx4 (hmin (x + 1) (by omega) (by omega))
      have := Pool.P0086.cert_actual hD hLv hlev (incrOf CA) (c := c) (x := x) (by rw [hE']; exact hx1) hx3 hx4
        A α β hα hβ hA'
      rw [hE', hxe, he, sum_Ico_incrOf CA c (by omega)] at this
      exact this
    · subst he
      have hpres : ∀ u, τ ≤ u → u < T → ∃ r' ℓ', c ∈ startPools E thr0 D Lv Bt ωs u
          (tpools E thr0 (Pool.P0061.cumL (incrOf CA)) θ R K D Lv Bt lev ωs φ u) r' ℓ' := by
        intro u hu1 hu2
        rcases hu1.lt_or_eq with hu | rfl
        · have hal : Alive E thr0 (Pool.P0061.cumL (incrOf CA)) θ R K D Lv Bt lev ωs φ u c := by
            by_contra hna; exact h ⟨u, hu, hu2.le, hna⟩
          exact salive_of_alive hD hLv hlev hal
        · exact hs0
      have := hA' c τ T hτ.le hpres
      rw [sum_Ico_incrOf CA c hτ.le] at this
      have hRα : α ≤ R * α := by
        have : (1 : ℝ) ≤ R := by exact_mod_cast hR1
        nlinarith
      linarith
  · have hc' : ωs c = false := by simpa using hs
    obtain ⟨-, x, hax, hxe, -, hin, hout⟩ := evict_spec hB hLv hlev cstar hE hthr hr hd he
    have := fo_cert hD hLv hlev s L hc' y (x := x) (by rw [hE']; exact hax) hin hout A α β hα hβ hA
    rw [hE', hxe] at this
    exact this

end FOCert

section FORun

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

/-- **Per-run regret bound of the FO process over the walk** (deterministic). With a learner within `α + β·len` of
the actual run's realized estimates of every present copy, and within `Bep` of the comparator per unit, the regret
against the comparator (true unit losses `g`) is at most P0086's bound plus the estimation errors of the records:
`Σ (A − g) ≤ (θ + Rα)·#records + βT + Bep·(bad length) + Σ_records z(len)`, if every covered record's data
overestimate the comparator's true loss by at most `z(len)` (`hz`). -/
theorem run_bound_FO (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (s : ℕ) (L : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s)
    (A : ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R)
    (hA : ∀ f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).pools r ℓ) →
      ∑ u ∈ Finset.Ico a b, A u ≤ Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f b -
        Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f a + α + β * ((b - a : ℕ) : ℝ))
    (g : ℕ → ℝ) (hBep : ∀ u, A u - g u ≤ Bep) (z : ℕ → ℝ) (hz0 : ∀ n, 0 ≤ z n)
    (hz : ∀ τ r e, Bt r ∣ τ → τ < T → r < D → evFO E thr0 θ R K D Lv Bt lev s L T cstar ωs φ y τ r = some e →
      recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ e -
        recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ τ - ∑ u ∈ Finset.Ico τ e, g u ≤ z (e - τ)) :
    let W := Pool.P0057.theWalk D T Bt (evFO E thr0 θ R K D Lv Bt lev s L T cstar ωs φ y)
    ∑ u ∈ Finset.range T, (A u - g u) ≤ (θ + R * α) * W.length + β * T +
      Bep * (((W.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) + (W.map fun x => z (Pool.P0057.len x)).sum := by
  intro W
  have hH := hyp_evWF (θ := θ) (R := R) (lev := lev) hB hLv hlev hT
    (Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y)
    (fun r τ => Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
      (forceF K φ (cstar r τ)) y) cstar hE hthr ωs φ
  obtain ⟨hc, hok, hsum, -⟩ := Pool.P0057.theWalk_spec hH
  rw [show Finset.range T = Finset.Ico 0 T from Finset.range_eq_Ico T]
  rw [Pool.P0086.chain_sum_Ico (fun u => A u - g u) W 0 hc]
  have hrec : ∀ x ∈ W, ∑ u ∈ Finset.Ico x.start x.stop, (A u - g u) ≤
      ((θ + R * α) + β * (Pool.P0057.len x : ℝ) + (if x.cov then 0 else Bep * (Pool.P0057.len x : ℝ))) +
        z (Pool.P0057.len x) := by
    intro x hx
    have hx' := hok x hx
    have hlen : ((x.stop - x.start : ℕ) : ℝ) = (Pool.P0057.len x : ℝ) := rfl
    have hz' := hz0 (Pool.P0057.len x)
    cases hcv : x.cov
    · simp only [Bool.false_eq_true, if_false]
      have h1 : ∑ u ∈ Finset.Ico x.start x.stop, (A u - g u) ≤ ∑ _u ∈ Finset.Ico x.start x.stop, Bep :=
        Finset.sum_le_sum fun u _ => hBep u
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hlen] at h1
      have h2 : (0 : ℝ) ≤ θ + R * α := by
        have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
        positivity
      have h3 : (0 : ℝ) ≤ β * (Pool.P0057.len x : ℝ) := by positivity
      linarith
    · simp only [if_true, add_zero]
      have hxT : x.start < T := lt_of_lt_of_le hx'.lt hx'.le
      have hcert := cert_evFO hB hLv hlev s L cstar hE hthr ωs φ y A α β hα hβ hθ hR1 hA
        hx'.inv.dvd hxT hx'.inv.lt (hx'.cov hcv)
      have hzx := hz x.start x.lvl x.stop hx'.inv.dvd hxT hx'.inv.lt (hx'.cov hcv)
      rw [Finset.sum_sub_distrib]
      rw [hlen] at hcert
      have : x.stop - x.start = Pool.P0057.len x := rfl
      rw [this] at hzx
      linarith
  calc (W.map fun x => ∑ u ∈ Finset.Ico x.start x.stop, (A u - g u)).sum
      ≤ (W.map fun x => ((θ + R * α) + β * (Pool.P0057.len x : ℝ) +
          (if x.cov then 0 else Bep * (Pool.P0057.len x : ℝ))) + z (Pool.P0057.len x)).sum := List.sum_le_sum hrec
    _ = (θ + R * α) * W.length + β * T + Bep * (((W.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) +
          (W.map fun x => z (Pool.P0057.len x)).sum := by
        have key : ∀ (M : List Pool.P0057.Rec), (M.map fun x => ((θ + R * α) + β * (Pool.P0057.len x : ℝ) +
            (if x.cov then 0 else Bep * (Pool.P0057.len x : ℝ))) + z (Pool.P0057.len x)).sum =
            (θ + R * α) * M.length + β * ((M.map Pool.P0057.len).sum : ℕ) +
              Bep * (((M.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) +
              (M.map fun x => z (Pool.P0057.len x)).sum := by
          intro M
          induction M with
          | nil => simp
          | cons y M ih =>
            rw [List.map_cons, List.sum_cons, ih]
            cases hy : y.cov <;> simp [hy] <;> ring
        rw [key, hsum]

end FORun

section FOClosed

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

/-- **Per-run FO regret bound in closed form**, for record errors `z(len) = a·√len + b`: with `H j` the bad walk
points of thread `j` (`nBad` of `evFO`),
`Σ (A − g) ≤ (θ + Rα + b)·(T/B 0 + Σ_{j<D−1} B j·H j/B (j+1)) + βT + Bep·B (D−1)·H (D−1)
  + a·(T/√(B 0) + Σ_{1≤j<D} B (j−1)·H (j−1)/√(B j))`. -/
theorem run_bound_FO_closed (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (s : ℕ) (L : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s)
    (A : ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hA : ∀ f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).pools r ℓ) →
      ∑ u ∈ Finset.Ico a b, A u ≤ Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f b -
        Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f a + α + β * ((b - a : ℕ) : ℝ))
    (g : ℕ → ℝ) (hBep : ∀ u, A u - g u ≤ Bep) (za zb : ℝ) (hza : 0 ≤ za) (hzb : 0 ≤ zb)
    (hz : ∀ τ r e, Bt r ∣ τ → τ < T → r < D → evFO E thr0 θ R K D Lv Bt lev s L T cstar ωs φ y τ r = some e →
      recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ e -
        recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ τ - ∑ u ∈ Finset.Ico τ e, g u ≤
          za * Real.sqrt ((e - τ : ℕ) : ℝ) + zb) :
    let H := Pool.P0057.nBad T Bt (evFO E thr0 θ R K D Lv Bt lev s L T cstar ωs φ y)
    ∑ u ∈ Finset.range T, (A u - g u) ≤
      (θ + R * α + zb) * (T / Bt 0 + ∑ j ∈ Finset.range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1)) +
        β * T + Bep * (Bt (D - 1) * H (D - 1) : ℕ) +
        za * (T / Real.sqrt (Bt 0) + ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) * H (j - 1) / Real.sqrt (Bt j)) := by
  intro H
  have hH := hyp_evWF (θ := θ) (R := R) (lev := lev) hB hLv hlev hT
    (Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y)
    (fun r τ => Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
      (forceF K φ (cstar r τ)) y) cstar hE hthr ωs φ
  have h1 := run_bound_FO (θ := θ) hB hLv hlev hT s L cstar hE hthr ωs φ y A α β Bep hα hβ hθ hR1 hA g hBep
    (fun n => za * Real.sqrt n + zb) (fun n => by positivity) hz
  simp only at h1
  set W := Pool.P0057.theWalk D T Bt (evFO E thr0 θ R K D Lv Bt lev s L T cstar ωs φ y) with hW
  have h2 := Pool.P0086.card_walk_le hH
  have h3 := Pool.P0086.sum_bad_len_le hH
  have h4 := Pool.P0057.sum_sqrt_le hH
  have hzsum : (W.map fun x => za * Real.sqrt (Pool.P0057.len x : ℝ) + zb).sum =
      za * (W.map fun x => Real.sqrt (Pool.P0057.len x : ℝ)).sum + zb * W.length := by
    clear h1 h2 h3 h4 hW
    induction W with
    | nil => simp
    | cons x M ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring
  rw [hzsum] at h1
  have hc0 : (0 : ℝ) ≤ θ + R * α := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    positivity
  have h3' : (((W.filter fun x => !x.cov).map Pool.P0057.len).sum : ℝ) ≤ (Bt (D - 1) * H (D - 1) : ℕ) := by
    exact_mod_cast h3
  calc ∑ u ∈ Finset.range T, (A u - g u)
      ≤ (θ + R * α) * W.length + β * T + Bep * (((W.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) +
          (za * (W.map fun x => Real.sqrt (Pool.P0057.len x : ℝ)).sum + zb * W.length) := h1
    _ = (θ + R * α + zb) * W.length + β * T +
          Bep * (((W.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) +
          za * (W.map fun x => Real.sqrt (Pool.P0057.len x : ℝ)).sum := by ring
    _ ≤ _ := by
        gcongr

end FOClosed

end Pool.P0112
