import Pool.P0200.ExtCount
import Pool.P0186.RecCert

/-!
# The rule hypotheses of P0186's walk bound for `dzRun` with a B̂-type rule (b″)

For P0176's `dzRun` (any layout, unit coins, sampling/filter bits) with the rule
`rhOf E Bmin Λ Bh u x h = [E x ≤ u] ∧ [Bmin ∣ u + 1] ∧ [Λ x u ≤ (h(u+1) − h(E x)) − (Bh(u+1) − Bh(E x))]`
(P0194's `rhD`, with `Bh` its B̂; P0200's `rhXR` with `BhE`):
* `dz_mem_aux_succ`, `dz_aux_mono`, `dz_E_lt_of_mem_aux`: retirement is by the rule, permanent, after entry;
* `dz_rule_of_first`: at a first retirement time the rule fired at the previous unit on the copy's own data;
* `dz_incr_retired`: a retired copy's data grow by `Bm` per unit (P0186's `hfake` when drawn losses are `≤ Bm`);
* **`dz_hrule`**: P0186's `hrule` for the mixed record runs (actual run for sampled copies, forced copy-last run for
  unsampled ones), with `Bhat u = Bh(u+1) − Bh u`, whenever P0186's margin `Λ'(thread, age)` is below the rule's
  margin `Λ x u` at the thread and age of the check.
-/

namespace Pool.P0207

open Pool.P0200
open Finset Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0156 Pool.P0176 Pool.P0168 Pool.P0186 Pool.P0105

/-- Rule (b″) with a B̂-type benchmark `Bh`, checked at multiples of `Bmin`. -/
noncomputable def rhOf {ι : Type} (E : ι → ℕ) (Bmin : ℕ) (Λ : ι → ℕ → ℝ) (Bh : ℕ → ℝ) (u : ℕ) (x : ι)
    (h : ℕ → ℝ) : Bool :=
  decide (E x ≤ u) && decide (Bmin ∣ u + 1) && decide (Λ x u ≤ h (u + 1) - h (E x) - (Bh (u + 1) - Bh (E x)))

section Rule

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (z : ℕ → Fin B → RT D sl)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

theorem dz_mem_aux_succ (a : ℕ) (x : ι) :
    x ∈ (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ (a + 1)).aux ↔
      x ∈ (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a).aux ∨
        (x ∈ members D Lv (startPools E thr0 D Lv Bt ωs a
            (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a).pools) ∧
          rh a x ((dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ (a + 1)).est x) = true) := by
  show x ∈ (dzUpd D Lv sl B Bm xr ℓr rh lay z a _ _ _).2 ↔ _
  simp only [dzUpd, dzUpdO, Finset.mem_union, Finset.mem_filter]
  rfl

theorem dz_aux_mono {a b : ℕ} (hab : a ≤ b) {x : ι}
    (hx : x ∈ (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a).aux) :
    x ∈ (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ b).aux := by
  induction b, hab using Nat.le_induction with
  | base => exact hx
  | succ b _ ih => exact (dz_mem_aux_succ Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ b x).2 (Or.inl ih)

/-- A copy retires only as a start-pool member, so after its entry. -/
theorem dz_E_lt_of_mem_aux (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι} :
    ∀ a, c ∈ (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a).aux → E c < a
  | 0, h => by simp [dzRun, gRun] at h
  | a + 1, h => by
    rcases (dz_mem_aux_succ Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a c).1 h with h1 | ⟨h1, -⟩
    · have := dz_E_lt_of_mem_aux hD hLv hlev a h1; omega
    · simp only [members, Finset.mem_biUnion, Finset.mem_range] at h1
      obtain ⟨r, -, ℓ, -, hc⟩ := h1
      have hok : BdOK E thr0 D Lv Bt a (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a).pools := by
        rw [gRun_pools_eq]
        exact tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (θ := θ) (R := R) (lev := lev) hD hLv hlev ωs φ a
      have hS := start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv hok ωs (x := a)
      have := (hS c r ℓ hc).1
      omega

/-- **At a first retirement time the rule fired** at the previous unit, on the copy's own updated data. -/
theorem dz_rule_of_first (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι} {e : ℕ}
    (he : E c < e) (hin : c ∈ (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ e).aux)
    (hmin : ∀ y, E c < y → y < e → c ∉ (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ y).aux) :
    rh (e - 1) c ((dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ e).est c) = true := by
  obtain ⟨a, rfl⟩ : ∃ a, e = a + 1 := ⟨e - 1, by omega⟩
  rcases (dz_mem_aux_succ Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a c).1 hin with h1 | ⟨-, h2⟩
  · exfalso
    have hlt := dz_E_lt_of_mem_aux Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ hD hLv hlev a h1
    exact hmin a hlt (by omega) h1
  · simpa using h2

/-- A retired copy's data grow by the fake increment `Bm` per unit. -/
theorem dz_incr_retired {f : ι} {u : ℕ} (hf : f ∈ (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ u).aux) :
    incrOf (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh lay z) ∅ ωs φ) u f = Bm := by
  unfold incrOf
  rw [gChat_succ]
  show _ + dzIncO D B Bm xr ℓr u _ _ f - _ = Bm
  simp only [dzIncO, if_pos hf]
  ring

end Rule

theorem sum_Ico_telescope (F : ℕ → ℝ) {a e : ℕ} (h : a ≤ e) : ∑ u ∈ Ico a e, (F (u + 1) - F u) = F e - F a := by
  induction e, h using Nat.le_induction with
  | base => simp
  | succ e he ih => rw [Finset.sum_Ico_succ_top he, ih]; ring

section Margin

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (z : ℕ → Fin B → RT D sl) (Bmin : ℕ) (Λ : ι → ℕ → ℝ) (Bh : ℕ → ℝ)

/-- The margin inequality at a first retirement, for one run (any layout and bits). -/
theorem dz_margin (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    {c : ι} {e : ℕ} (he : E c < e)
    (hin : c ∈ (dzRun Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) E thr0 θ R K Bt lev lay z ωs φ e).aux)
    (hmin : ∀ y, E c < y → y < e →
      c ∉ (dzRun Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) E thr0 θ R K Bt lev lay z ωs φ y).aux) :
    Λ c (e - 1) ≤ ∑ u ∈ Ico (E c) e, incrOf (gChat E thr0 θ R K D Lv Bt lev
        (dzUpd D Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) lay z) ∅ ωs φ) u c -
      ∑ u ∈ Ico (E c) e, (Bh (u + 1) - Bh u) := by
  have hr := dz_rule_of_first Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) E thr0 θ R K Bt lev lay z ωs φ hD hLv hlev he hin hmin
  simp only [rhOf, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨-, hΛ⟩ := hr
  have he1 : e - 1 + 1 = e := by omega
  rw [he1] at hΛ
  have hf1 := gEst_frozen E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) lay z) ∅ ωs φ c e le_rfl
  have hf2 := gEst_frozen E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) lay z) ∅ ωs φ c e
    he.le
  unfold incrOf
  rw [sum_Ico_telescope _ he.le, sum_Ico_telescope _ he.le]
  rw [hf1, hf2] at hΛ
  exact hΛ

attribute [local instance] Pool.P0082.coinFintype

/-- **P0186's `hrule` for `dzRun` with a B̂-type rule.** For the mixed record runs (actual entry-order run if the copy
is sampled, its forced copy-last run otherwise), a first retirement at `e` gives P0186's margin
`Λ'(min(curT c e, D−1), e − E c) ≤ Σ_{[E c, e)} (record data increments) − Σ_{[E c, e)} Bhat` with
`Bhat u = Bh(u+1) − Bh u`, whenever `Λ'` at the thread and age of every check is at most the rule's margin. -/
theorem dz_hrule (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (T : ℕ) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (Λ' : ℕ → ℕ → ℝ)
    (hΛ : ∀ c u, Λ' (min (curT E thr0 D Bt c (u + 1)) (D - 1)) (u + 1 - E c) ≤ Λ c u) (c : ι) (e : ℕ)
    (hret : RetAt E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) (sortLay sl) z) ∅
      (fun c' => dzUpd D Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) (lastLay sl c') z) (fun _ => ∅) T ωs φ c e) :
    Λ' (min (curT E thr0 D Bt c e) (D - 1)) (e - E c) ≤
      ∑ u ∈ Ico (E c) e, incrOf (recD E thr0 θ R K D Lv Bt lev
        (dzUpd D Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) (sortLay sl) z) ∅
        (fun c' => dzUpd D Lv sl B Bm xr ℓr (rhOf E Bmin Λ Bh) (lastLay sl c') z) (fun _ => ∅) ωs φ c) u c -
      ∑ u ∈ Ico (E c) e, (Bh (u + 1) - Bh u) := by
  have hstep : ∀ {e : ℕ}, E c < e → Λ' (min (curT E thr0 D Bt c e) (D - 1)) (e - E c) ≤ Λ c (e - 1) := by
    intro e he
    have := hΛ c (e - 1)
    rwa [show e - 1 + 1 = e by omega] at this
  unfold RetAt at hret
  unfold recD
  split_ifs at hret ⊢ with hs
  · obtain ⟨he, -, hin, hmin⟩ := aRet_spec hret
    exact (hstep he).trans (dz_margin Lv sl B Bm xr ℓr E thr0 θ R K Bt lev z Bmin Λ Bh hD hLv hlev (sortLay sl) ωs φ
      he hin hmin)
  · obtain ⟨he, -, hin, hmin⟩ := retT_spec hret
    exact (hstep he).trans (dz_margin Lv sl B Bm xr ℓr E thr0 θ R K Bt lev z Bmin Λ Bh hD hLv hlev (lastLay sl c)
      (forceS ωs c) (forceF K φ c) he hin hmin)

end Margin

end Pool.P0207
