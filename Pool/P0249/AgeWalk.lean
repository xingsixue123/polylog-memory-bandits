import Pool.P0235.ActOcc
import Pool.P0242.ActOcc
import Pool.P0238.Count

/-!
# The walk's margin condition is needed only at ages a copy can reach in its current thread
-/

open Finset Pool.P0156 Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0168
  Pool.P0135 Pool.P0105 Pool.P0186

namespace Pool.P0249

section Age

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {D : ℕ} {Bt : ℕ → ℕ}

/-- **Deterministic age bound.** A copy whose current thread at `e > E c` is `j ≥ 1` has been alive at most
`Σ_{i∈[j,Θn]} Bt(i−1)` rounds (P0171's occupancy: at most `Bt(i−1)` rounds in each thread `i ≥ 1`; threads only get
coarser, so every earlier round was in a thread `≥ j`). -/
theorem age_le (hB : ∀ i, 0 < Bt i) (Θn : ℕ) (c : ι) (hΘ : thr0 c ≤ Θn) {e j : ℕ} (hj : 1 ≤ j)
    (hEe : E c ≤ e) (hcur : curT E thr0 D Bt c e = j) :
    e - E c ≤ ∑ i ∈ Finset.Icc j Θn, Bt (i - 1) := by
  classical
  have hmaps : ∀ u ∈ Finset.Ico (E c) e, curT E thr0 D Bt c u ∈ Finset.Icc j Θn := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    rw [Finset.mem_Icc]
    constructor
    · rw [← hcur]
      exact curT_mono (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c hu.2.le hu.1
    · exact (curT_le_thr0 (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c u).trans hΘ
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Nat.card_Ico] at hcard
  rw [hcard]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi1 : 1 ≤ i := le_trans hj (Finset.mem_Icc.mp hi).1
  exact Pool.P0171.card_curT_eq_le (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c hi1 (hB _) (E c) e le_rfl

/-- The age bound in P0238's `lenOf` form, for every thread (`T` for the coarsest). -/
theorem age_le_lenOf (hB : ∀ i, 0 < Bt i) (Θn T : ℕ) (c : ι) (hΘ : thr0 c ≤ Θn) {e : ℕ}
    (hEe : E c ≤ e) (heT : e ≤ T) :
    e - E c ≤ Pool.P0238.lenOf Θn T Bt (curT E thr0 D Bt c e) := by
  unfold Pool.P0238.lenOf
  split_ifs with hj
  · exact age_le hB Θn c hΘ hj hEe rfl
  · omega

end Age

section Walk

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E : ι → ℕ} {thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}
  {upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {aux0 : Finset ι}
  {U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {A0 : ι → Finset ι}
  {T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}

/-- **P0186's per-run bound with the margin condition only at reachable ages** (`hΛ` for `n ≤ lenOf j`, P0238's
deterministic lifetime of thread `j`): a (b″)-record of thread `j` retires its copy at an age `≤ lenOf j`
(`age_le_lenOf`), which is the only place `hΛ` is used. -/
theorem run_bound_mix_age (Θn : ℕ) (hΘn : ∀ c, thr0 c ≤ Θn) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (hT : Bt 0 ∣ T)
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
    (hΛ : ∀ j n, n ≤ Pool.P0238.lenOf Θn T Bt j → Ψ + α + Γ + WD n + WB n + W n + w j ≤ Λ j n)
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
    obtain ⟨hlt1, heT, hcost⟩ := hcert
    -- the age at retirement is at most the deterministic lifetime of its thread
    obtain ⟨-, -, -, hiq⟩ := outMix_bev hout
    have hcurle : curT E thr0 D Bt cc e ≤ D - 1 := by
      have h1 := curT_le_thr0 (E := E) (thr0 := thr0) (D := D) (Bt := Bt) cc e
      have h2 : thr0 cc = x.lvl := hthr x.lvl x.start hlvl hdvd hsT
      omega
    have hi : i = curT E thr0 D Bt cc e := by rw [hiq, min_eq_left hcurle]
    have hage := age_le_lenOf (E := E) (thr0 := thr0) (D := D) hB.pos Θn T cc (hΘn cc) hlt1.le heT
    rw [← hi] at hage
    rw [hEc, he] at hcost
    rw [hEc, he] at hage
    rw [Finset.sum_congr rfl fun u _ => by rw [hg x.lvl x.start u hlvl hdvd hsT]] at hcost
    have hl := hΛ i (x.stop - x.start) hage
    simp only [Finset.sum_sub_distrib] at hcost ⊢
    linarith
  · intro x hx hfb
    have hfr := hgrid x hx
    simp [Pool.P0184.freeBad, hfr] at hfb
    split at hfb <;> simp_all

end Walk

section Occ

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0220 Pool.P0226 Pool.P0235

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool) (T : ℕ)
  (rc0 : RC (withAlg P η L N G γ wE ρr))

local notation "QQ" => withAlg P η L N G γ wE ρr

/-- **P0235's per-run ALG-term bound with the margin condition only at reachable ages** (`hΛ` for `m ≤ lenOf j`),
via `run_bound_mix_age`; otherwise identical to P0235's `run_bound_occ`. -/
theorem run_bound_occ_age (Θn : ℕ) (hΘn : ∀ c, (QQ).thr0 c ≤ Θn) (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (withAlg P η L N G γ wE ρr).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (withAlg P η L N G γ wE ρr).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt0 : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hlay : (withAlg P η L N G γ wE ρr).lay = Pool.P0176.sortLay (withAlg P η L N G γ wE ρr).sl)
    (hS : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f) (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl
      (sp (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u))
    (hB : Pool.P0158.GoodV (Pool.P0216.DB (withAlg P η L N G γ wE ρr) ℓ rc0) (fun _ _ => true)
      (fun _ => (withAlg P η L N G γ wE ρr).cB) (Pool.P0158.rmax1 (fun _ => (withAlg P η L N G γ wE ρr).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
      (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hXm : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
      (YB P η L N G γ wE ρr ℓ rc0) (bPolX P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hA : Pool.P0149.StepGood (Pool.P0227.DT P η L N G γ wE ρr ℓ ωs φ rc0 κ) (fun _ _ => true) (Lt / κ) T
      (Pool.P0203.pre _ ω T))
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hgF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false →
      Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.gateS (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.rS (withAlg P η L N G γ wE ρr) (cstar j a))
        (Pool.P0158.rmax1 (Pool.P0203.rS (withAlg P η L N G γ wE ρr) (cstar j a))) Ls T
        (Pool.P0203.pre (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ω T))
    (hfF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false → ∀ u, u < T →
      Pool.P0176.Fits (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl
        (sp (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ ω (Pool.P0065.forceS ωs (cstar j a))
          (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) u))
    (Λ' : ℕ → ℕ → ℝ) (hΛ' : ∀ c u, Λ' (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤
      (QQ).Λ c u)
    (ff aa : ℕ → ℝ) (cc : ℝ) (w : ℕ → ℝ) (ha : ∀ j < (QQ).D, 0 ≤ aa j) (hc0 : 0 ≤ cc)
    (hbig : ∀ j < (QQ).D, ∀ m : ℕ, (QQ).Bt j ≤ m → ff m ≤ m * aa j)
    (hsmall : ∀ m : ℕ, m < (QQ).Bt ((QQ).D - 1) → ff m ≤ cc)
    (hf : ∀ m : ℕ, (QQ).θ + (QQ).R * (2 * αT (ι := ι) η L T δ + 2 * (Lc / (2 * (wE * γ))) +
        Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m) + Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m + Lt / κ ≤ ff m)
    (hfB : (1 : ℝ) * (QQ).Bt ((QQ).D - 1) ≤ ff ((QQ).Bt ((QQ).D - 1)))
    (hΛ : ∀ j (m : ℕ), m ≤ Pool.P0238.lenOf Θn T (QQ).Bt j → Lt / κ + αT (ι := ι) η L T δ + Lc / (2 * (wE * γ)) + 0 +
        Pool.P0158.widV (m * (withAlg P η L N G γ wE ρr).cB) (max 1 (withAlg P η L N G γ wE ρr).cB) Lb +
        Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m + w j ≤ Λ' j m)
    (hw : ∀ i < (QQ).D, ∑ j ∈ Finset.Ico 1 (QQ).D, (if i ≤ j - 1 then ((QQ).Bt (j - 1) : ℝ) * aa j else 0) +
      (if i ≤ (QQ).D - 1 then cc else 0) ≤ w i) :
    ∑ u ∈ Finset.range T, (aPt P η L N G γ wE ρr ℓ ω ωs φ T u - gT ℓ T i u -
        (η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u + slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u)) ≤
      T * aa 0 + ∑ j ∈ Finset.Ico 1 (QQ).D, ((QQ).Bt (j - 1) : ℝ) *
          (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
            (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅
            (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c') (zc (withAlg P η L N G γ wE ρr) ω))
            (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) (j - 1) : ℝ) * aa j +
        (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
            (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅
            (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c') (zc (withAlg P η L N G γ wE ρr) ω))
            (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) ((QQ).D - 1) : ℝ) * cc := by
  have H := actHyp_occ P η L N G γ wE ρr ℓ ω ωs φ T rc0 hD hLv hlev hL hN hη hδ hρr hγ hwE0 hwE hTL hcB0 hLs hLb
    hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hS hfit hB hX hXm hA
  have hWm := Pool.P0222.Wocc_mono (xmin := xmin) (ρ := ρ) (nn := nn) (TT := TT) (Θ := Θ) hLs hM
  have hW0 : ∀ m, 0 ≤ Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m := fun m => by
    unfold Pool.P0222.Wocc; have := Real.sqrt_nonneg (Ls * ((m : ℝ) * M + Θ * (ρ * TT / nn))); positivity
  refine run_bound_mix_age Θn hΘn (U := fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr
      (ℓr (withAlg P η L N G γ wE ρr) ℓ) (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c')
      (zc (withAlg P η L N G γ wE ρr) ω)) (A0 := fun _ => ∅) (Bep := 1) hBt hLv hlev hT cstar hE hthr ?hcoup
    (ℓt P η L N G γ wE ρr ℓ T) (fun u x => cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x)) (gT ℓ T i) ?hg
    _ _ _ _ _ _ _ _ _ _ Λ' (αT_nonneg (ι := ι) η L T hη hδ) (div_nonneg hLc (by positivity)) hW0 hWm ?hθ ?hR1 H
    ?hup ?hrule ?hBep ff aa cc w ha hc0 hbig hsmall hf hfB hΛ hw
  case hcoup =>
    intro j a hj hdv haT hc
    have := Pool.P0197.coup_dz (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
      (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).Bt (QQ).lev (zc (withAlg P η L N G γ wE ρr) ω) hc φ
    rw [hlay]
    exact this
  case hg =>
    intro j a u hj hdv haT
    unfold ℓt gT ℓr
    rw [show (withAlg P η L N G γ wE ρr).arm (cstar j a) = i from harm j a hj hdv haT]
  case hθ => exact hθ
  case hR1 => exact hR1
  case hBep =>
    intro u
    have h1 : aPt P η L N G γ wE ρr ℓ ω ωs φ T u ≤ 1 := by
      unfold aPt; split_ifs
      · exact aPol_le_one P η L N G γ wE ρr ℓ ω ωs φ u
      · exact zero_le_one
    have h2 : 0 ≤ gT ℓ T i u := by unfold gT; split_ifs <;> positivity
    have h3 : 0 ≤ η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u :=
      mul_nonneg (by positivity) (VR_nonneg P η L N G γ wE ρr ℓ ω ωs φ T u)
    have h4 := slT_nonneg P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u
    linarith
  case hup =>
    intro j a hj hdv haT e hae heT hnr
    have hEa := hE j a hj hdv haT
    have h := Pool.P0222.hup_occ (withAlg P η L N G γ wE ρr) ℓ ω ωs φ hD hLv hlev rc0 (cstar j a) hLs hxm hxm1 hxr
      hn hTT hM hρ0 hBt0 hρ hx0 hx (hΘ (cstar j a)) T
      (fun _ => hS (cstar j a)) (fun hs u hu => hfit u hu) (hgF j a hj hdv haT) (hfF j a hj hdv haT) e (by omega) heT
      (by rw [hEa]; exact hnr)
    rw [hEa] at h
    have e1 : ∑ u ∈ Ico a e, ℓr (withAlg P η L N G γ wE ρr) ℓ u (cstar j a) =
        ∑ u ∈ Ico a e, ℓt P η L N G γ wE ρr ℓ T u (cstar j a) :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold ℓt; rw [if_pos (by omega)]
    rw [e1] at h
    exact h
  case hrule =>
    intro j a hj hdv haT e hret
    have hEa := hE j a hj hdv haT
    have h := Pool.P0207.dz_hrule (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ) (QQ).E (QQ).thr0
      (QQ).θ (QQ).R (QQ).K (QQ).Bt (QQ).lev (zc (withAlg P η L N G γ wE ρr) ω) (QQ).Bmin (QQ).Λ
      (Bh (withAlg P η L N G γ wE ρr) ℓ ω) hD hLv hlev T ωs φ Λ' hΛ' (cstar j a) e (by rw [← hlay]; exact hret)
    rw [← hlay, hEa] at h
    have e1 : ∑ u ∈ Ico a e, (Bh (withAlg P η L N G γ wE ρr) ℓ ω (u + 1) - Bh (withAlg P η L N G γ wE ρr) ℓ ω u) =
        ∑ u ∈ Ico a e, Pool.P0216.incBD (withAlg P η L N G γ wE ρr) ℓ ω u :=
      Finset.sum_congr rfl fun u _ => by
        rw [Pool.P0216.Bh_sum (withAlg P η L N G γ wE ρr) ℓ ω u (u + 1) (Nat.le_succ u)]
        simp
    rw [e1] at h
    exact h

end Occ

section OccG

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0231 Pool.P0242
open Pool.P0226 (sum_trunc αT αT_nonneg widV_mono2 widV_nonneg gT)

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool) (T : ℕ)
  (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

/-- **P0242's per-run ALG-term bound (ALG `withAlgG`, simulated by P0236's finite twin) with the margin condition only
at reachable ages**, via `run_bound_mix_age`; otherwise identical to P0242's `run_bound_occ`. -/
theorem run_bound_occG_age (Θn : ℕ) (hΘn : ∀ c, (QQ).thr0 c ≤ Θn) (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (Pool.P0225.withAlgG P η L N G γ wE ρG).IsLaw) (hN : 0 < (Pool.P0225.withAlgG P η L N G γ wE ρG).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρG : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt0 : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hlay : (Pool.P0225.withAlgG P η L N G γ wE ρG).lay = Pool.P0176.sortLay (Pool.P0225.withAlgG P η L N G γ wE ρG).sl)
    (hS : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f) (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
      (sp (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u))
    (hB : Pool.P0158.GoodV (Pool.P0216.DB (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ rc0) (fun _ _ => true)
      (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) (Pool.P0158.rmax1 (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN) (lossX P η L N G γ wE ρG ℓ x)
      (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hXm : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hA : Pool.P0149.StepGood (Pool.P0240.DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lt / κ) T
      (Pool.P0203.pre _ ω T))
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hgF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false →
      Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.gateS (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a))
        (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a))) Ls T
        (Pool.P0203.pre (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ω T))
    (hfF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false → ∀ u, u < T →
      Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
        (sp (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ ω (Pool.P0065.forceS ωs (cstar j a))
          (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) u))
    (Λ' : ℕ → ℕ → ℝ) (hΛ' : ∀ c u, Λ' (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤
      (QQ).Λ c u)
    (ff aa : ℕ → ℝ) (cc : ℝ) (w : ℕ → ℝ) (ha : ∀ j < (QQ).D, 0 ≤ aa j) (hc0 : 0 ≤ cc)
    (hbig : ∀ j < (QQ).D, ∀ m : ℕ, (QQ).Bt j ≤ m → ff m ≤ m * aa j)
    (hsmall : ∀ m : ℕ, m < (QQ).Bt ((QQ).D - 1) → ff m ≤ cc)
    (hf : ∀ m : ℕ, (QQ).θ + (QQ).R * (2 * αT (ι := ι) η L T δ + 2 * (Lc / (2 * (wE * γ))) +
        Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m) + Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m + Lt / κ ≤ ff m)
    (hfB : (1 : ℝ) * (QQ).Bt ((QQ).D - 1) ≤ ff ((QQ).Bt ((QQ).D - 1)))
    (hΛ : ∀ j (m : ℕ), m ≤ Pool.P0238.lenOf Θn T (QQ).Bt j → Lt / κ + αT (ι := ι) η L T δ + Lc / (2 * (wE * γ)) + 0 +
        Pool.P0158.widV (m * (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) (max 1 (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) Lb +
        Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m + w j ≤ Λ' j m)
    (hw : ∀ i < (QQ).D, ∑ j ∈ Finset.Ico 1 (QQ).D, (if i ≤ j - 1 then ((QQ).Bt (j - 1) : ℝ) * aa j else 0) +
      (if i ≤ (QQ).D - 1 then cc else 0) ≤ w i) :
    ∑ u ∈ Finset.range T, (aPt P η L N G γ wE ρG ℓ ω ωs φ T u - gT ℓ T i u -
        (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u + slT P η L N G γ wE ρG ℓ ω ωs φ T rc0 κ u)) ≤
      T * aa 0 + ∑ j ∈ Finset.Ico 1 (QQ).D, ((QQ).Bt (j - 1) : ℝ) *
          (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
            (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ)
              (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω) (QQ).lay (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω)) ∅
            (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ)
              (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω) (Pool.P0176.lastLay (QQ).sl c') (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω))
            (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) (j - 1) : ℝ) * aa j +
        (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
            (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ)
              (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω) (QQ).lay (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω)) ∅
            (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ)
              (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω) (Pool.P0176.lastLay (QQ).sl c') (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω))
            (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) ((QQ).D - 1) : ℝ) * cc := by
  have H := actHyp_occ P η L N G γ wE ρG ℓ ω ωs φ T rc0 hD hLv hlev hL hN hη hδ hρG hγ hwE0 hwE hTL hcB0 hLs hLb
    hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hS hfit hB hX hXm hA
  have hWm := Pool.P0222.Wocc_mono (xmin := xmin) (ρ := ρ) (nn := nn) (TT := TT) (Θ := Θ) hLs hM
  have hW0 : ∀ m, 0 ≤ Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m := fun m => by
    unfold Pool.P0222.Wocc; have := Real.sqrt_nonneg (Ls * ((m : ℝ) * M + Θ * (ρ * TT / nn))); positivity
  refine run_bound_mix_age Θn hΘn (U := fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr
      (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ) (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω) (Pool.P0176.lastLay (QQ).sl c')
      (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω)) (A0 := fun _ => ∅) (Bep := 1) hBt hLv hlev hT cstar hE hthr ?hcoup
    (ℓt P η L N G γ wE ρG ℓ T) (fun u x => Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u (some x)) (gT ℓ T i) ?hg
    _ _ _ _ _ _ _ _ _ _ Λ' (αT_nonneg (ι := ι) η L T hη hδ) (div_nonneg hLc (by positivity)) hW0 hWm ?hθ ?hR1 H
    ?hup ?hrule ?hBep ff aa cc w ha hc0 hbig hsmall hf hfB hΛ hw
  case hcoup =>
    intro j a hj hdv haT hc
    have := Pool.P0197.coup_dz (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ)
      (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω) (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).Bt (QQ).lev (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω) hc φ
    rw [hlay]
    exact this
  case hg =>
    intro j a u hj hdv haT
    unfold ℓt gT ℓr
    rw [show (Pool.P0225.withAlgG P η L N G γ wE ρG).arm (cstar j a) = i from harm j a hj hdv haT]
  case hθ => exact hθ
  case hR1 => exact hR1
  case hBep =>
    intro u
    have h1 : aPt P η L N G γ wE ρG ℓ ω ωs φ T u ≤ 1 := by
      unfold aPt; split_ifs
      · exact Pool.P0228.aPol_le_one (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ ω u
      · exact zero_le_one
    have h2 : 0 ≤ gT ℓ T i u := by unfold gT; split_ifs <;> positivity
    have h3 : 0 ≤ η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u :=
      mul_nonneg (by positivity) (VR_nonneg P η L N G γ wE ρG ℓ ω ωs φ T u)
    have h4 := slT_nonneg P η L N G γ wE ρG ℓ ω ωs φ T rc0 κ u
    linarith
  case hup =>
    intro j a hj hdv haT e hae heT hnr
    have hEa := hE j a hj hdv haT
    have h := Pool.P0222.hup_occ (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ hD hLv hlev rc0 (cstar j a) hLs hxm hxm1 hxr
      hn hTT hM hρ0 hBt0 hρ hx0 hx (hΘ (cstar j a)) T
      (fun _ => hS (cstar j a)) (fun hs u hu => hfit u hu) (hgF j a hj hdv haT) (hfF j a hj hdv haT) e (by omega) heT
      (by rw [hEa]; exact hnr)
    rw [hEa] at h
    have e1 : ∑ u ∈ Ico a e, ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ u (cstar j a) =
        ∑ u ∈ Ico a e, ℓt P η L N G γ wE ρG ℓ T u (cstar j a) :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold ℓt; rw [if_pos (by omega)]
    rw [e1] at h
    exact h
  case hrule =>
    intro j a hj hdv haT e hret
    have hEa := hE j a hj hdv haT
    have h := Pool.P0207.dz_hrule (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ) (QQ).E (QQ).thr0
      (QQ).θ (QQ).R (QQ).K (QQ).Bt (QQ).lev (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω) (QQ).Bmin (QQ).Λ
      (Bh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω) hD hLv hlev T ωs φ Λ' hΛ' (cstar j a) e (by rw [← hlay]; exact hret)
    rw [← hlay, hEa] at h
    have e1 : ∑ u ∈ Ico a e, (Bh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω (u + 1) - Bh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u) =
        ∑ u ∈ Ico a e, Pool.P0216.incBD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u :=
      Finset.sum_congr rfl fun u _ => by
        rw [Pool.P0216.Bh_sum (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u (u + 1) (Nat.le_succ u)]
        simp
    rw [e1] at h
    exact h

end OccG

end Pool.P0249
