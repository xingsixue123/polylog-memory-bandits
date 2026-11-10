import Pool.P0186.RecCert

/-!
# Per-run regret bound of Design Z's pool process over P0135's walk (P0166's C9, deterministic part)

`hypB_outMix_grid` + `cov_cert_mix` + `bev_cert_mix` (the margin pays the credit `w j`) + P0184's `walk_sum_fin`.
-/

namespace Pool.P0186

open Finset Pool.P0156 Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0168
  Pool.P0135 Pool.P0105

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E : ι → ℕ} {thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}
  {upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {aux0 : Finset ι}
  {U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {A0 : ι → Finset ι}
  {T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}
/-- **Per-run bound.** For every run (fixed coins) satisfying the concentration hypotheses, the learner's true loss
minus the comparator's loss minus the variance budget is at most
`T·a 0 + Σ_{1≤j<D} Bt(j-1)·nBad(j-1)·a j + nBad(D-1)·c`, where `nBad j` counts the level-`j` epoch starts whose
comparator copy (mixed outcome) is bad. -/
theorem run_bound_mix (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (hT : Bt 0 ∣ T)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < D → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j < D → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (hcoup : ∀ j a, j < D → Bt j ∣ a → a < T → ωs (cstar j a) = false →
      Coup E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ (cstar j a))
    (ℓ cI : ℕ → ι → ℝ) (g : ℕ → ℝ) (hg : ∀ j a u, j < D → Bt j ∣ a → a < T → ℓ u (cstar j a) = g u)
    (A Atrue V cB drawn bpol Bhat : ℕ → ℝ) {α Γ Ψ Bep : ℝ} (W WD WB : ℕ → ℝ) (Λ : ℕ → ℕ → ℝ)
    (hα : 0 ≤ α) (hΓ : 0 ≤ Γ) (hW0 : ∀ n, 0 ≤ W n) (hWm : Monotone W) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R)
    (H : ActHyp E thr0 θ R K D Lv Bt lev upd aux0 ωs φ ℓ cI A Atrue V cB drawn bpol Bhat α Γ Ψ W WD WB)
    (hup : ∀ j a, j < D → Bt j ∣ a → a < T → ∀ e, a ≤ e → e ≤ T →
      (∀ u, a < u → u < e → cstar j a ∉ recAux E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ (cstar j a) u) →
      ∑ u ∈ Ico a e, incrOf (recD E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ (cstar j a)) u (cstar j a) ≤
        ∑ u ∈ Ico a e, ℓ u (cstar j a) + W (e - a))
    (hrule : ∀ j a, j < D → Bt j ∣ a → a < T → ∀ e,
      RetAt E thr0 θ R K D Lv Bt lev upd aux0 U A0 T ωs φ (cstar j a) e →
      Λ (min (curT E thr0 D Bt (cstar j a) e) (D - 1)) (e - a) ≤
        ∑ u ∈ Ico a e, incrOf (recD E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ (cstar j a)) u (cstar j a) -
          ∑ u ∈ Ico a e, Bhat u)
    (hBep : ∀ u, Atrue u - g u - V u ≤ Bep)
    (f a : ℕ → ℝ) (c : ℝ) (w : ℕ → ℝ)
    (ha : ∀ j < D, 0 ≤ a j) (hc0 : 0 ≤ c)
    (hbig : ∀ j < D, ∀ n : ℕ, Bt j ≤ n → f n ≤ n * a j)
    (hsmall : ∀ n : ℕ, n < Bt (D - 1) → f n ≤ c)
    (hf : ∀ n, θ + R * (2 * α + 2 * Γ + W n) + W n + Ψ ≤ f n)
    (hfB : Bep * Bt (D - 1) ≤ f (Bt (D - 1)))
    (hΛ : ∀ j n, Ψ + α + Γ + WD n + WB n + W n + w j ≤ Λ j n)
    (hw : ∀ i < D, ∑ j ∈ Finset.Ico 1 D, (if i ≤ j - 1 then (Bt (j - 1) : ℝ) * a j else 0) +
      (if i ≤ D - 1 then c else 0) ≤ w i) :
    ∑ u ∈ Finset.range T, (Atrue u - g u - V u) ≤
      T * a 0 + ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) *
          (nBadB T Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev upd aux0 U A0 (D - 1) T ωs φ (cstar r τ))
            (j - 1) : ℝ) * a j +
        (nBadB T Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev upd aux0 U A0 (D - 1) T ωs φ (cstar r τ))
          (D - 1) : ℝ) * c := by
  have hD := hB.hD
  have hH := hypB_outMix_grid (θ := θ) (R := R) (upd := upd) (aux0 := aux0) (ωs := ωs) (φ := φ)
    hB hLv hlev hT cstar U A0 hE hthr
  have hB1 : Bt (D - 1) = 1 := hB.last
  obtain ⟨-, hok, -, -⟩ := theWalkB_spec hH
  have hgrid : ∀ x ∈ theWalkB D T Bt
      (fun τ r => outMix E thr0 θ R K D Lv Bt lev upd aux0 U A0 (D - 1) T ωs φ (cstar r τ)) (fun _ => .bad),
      x.free = false := fun x hx => walkB_grid_free hB1 _ 0 0 x hx
  have key := Pool.P0184.walk_sum_fin hH (fun u => Atrue u - g u - V u) f a c 0 w ha hc0 hbig hsmall ?_ ?_ ?_ hw
  · simpa using key
  · -- counted records
    intro x hx hct
    have hfr := hgrid x hx
    obtain ⟨hlvl, hdvd, hout⟩ := (hok x hx).grid hfr
    have hlt := (hok x hx).lt
    have hle := (hok x hx).le
    have hsT : x.start < T := lt_of_lt_of_le hlt hle
    rcases hx' : x.out with e | ⟨e, j⟩ | _
    · have he := (hok x hx).cov e hx'
      rw [hx'] at hout
      set cc := cstar x.lvl x.start
      have hEc := hE x.lvl x.start hlvl hdvd hsT
      have hcert := cov_cert_mix (upd := upd) (aux0 := aux0) (U := U) (A0 := A0) (T := T) hD hLv hlev
        (c := cc) (by rw [hthr x.lvl x.start hlvl hdvd hsT]; exact hlvl)
        (by rw [hthr x.lvl x.start hlvl hdvd hsT, hEc]; exact hdvd) (by rw [hEc]; exact hsT.le)
        (hcoup x.lvl x.start hlvl hdvd hsT) H hα hΓ hW0 hWm hθ hR1
        (by rw [hEc]; exact hup x.lvl x.start hlvl hdvd hsT) hout
      obtain ⟨-, -, hcost⟩ := hcert
      rw [hEc, he] at hcost
      rw [Finset.sum_congr rfl fun u _ => by rw [hg x.lvl x.start u hlvl hdvd hsT]] at hcost
      have hfl := hf (x.stop - x.start)
      simp only [Finset.sum_sub_distrib] at hcost ⊢
      unfold len
      linarith
    · simp [counted, hx'] at hct
    · obtain ⟨hst, hl1⟩ := (hok x hx).bad hx'
      rw [hfr] at hst; simp only [Bool.false_eq_true, if_false] at hst
      have hlv : x.lvl = D - 1 := by have := hl1 hfr; omega
      rw [hlv] at hst
      have hlen : len x = Bt (D - 1) := by unfold len; omega
      have h1 : ∑ u ∈ Ico x.start x.stop, (Atrue u - g u - V u) ≤ ∑ _u ∈ Ico x.start x.stop, Bep :=
        Finset.sum_le_sum fun u _ => hBep u
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
      rw [hlen]
      have : ((x.stop - x.start : ℕ) : ℝ) = (Bt (D - 1) : ℝ) := by rw [hst]; push_cast; simp
      rw [this] at h1
      linarith
  · -- (b″)-records
    intro x hx e i hx'
    have hfr := hgrid x hx
    obtain ⟨hlvl, hdvd, hout⟩ := (hok x hx).grid hfr
    have hlt := (hok x hx).lt
    have hle := (hok x hx).le
    have hsT : x.start < T := lt_of_lt_of_le hlt hle
    have he := (hok x hx).bev e i hx'
    rw [hx'] at hout
    set cc := cstar x.lvl x.start
    have hEc := hE x.lvl x.start hlvl hdvd hsT
    have hcert := bev_cert_mix (U := U) (A0 := A0) (T := T) (c := cc) Λ H
      (by rw [hEc]; exact hrule x.lvl x.start hlvl hdvd hsT)
      (by rw [hEc]; exact hup x.lvl x.start hlvl hdvd hsT) hout
    obtain ⟨-, -, hcost⟩ := hcert
    rw [hEc, he] at hcost
    rw [Finset.sum_congr rfl fun u _ => by rw [hg x.lvl x.start u hlvl hdvd hsT]] at hcost
    have hl := hΛ i (x.stop - x.start)
    simp only [Finset.sum_sub_distrib] at hcost ⊢
    linarith
  · intro x hx hfb
    have hfr := hgrid x hx
    simp [Pool.P0184.freeBad, hfr] at hfb
    split at hfb <;> simp_all

end Pool.P0186
