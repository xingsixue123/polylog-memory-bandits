import Pool.P0186.OutMix
import Pool.P0184.WalkFin
import Pool.P0148.Cert
import Pool.P0160.RetCert
import Pool.P0074.Cert
import Pool.P0105.FOConc

/-!
# Record certificates of the mixed walk outcomes (Design Z, P0166's C9, deterministic part)
-/

namespace Pool.P0186

open Finset Pool.P0156 Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0168
  Pool.P0135

section NoFree

variable {R T : ℕ} {B : ℕ → ℕ} {t : ℕ → ℕ → Out} {g : ℕ → Out}
/-- With a one-unit finest epoch every walk position is on the grid, so no record is free. -/
theorem walkB_grid_free (hB1 : B (R - 1) = 1) :
    ∀ (fuel u ℓ : ℕ), ∀ x ∈ walkB R T B t g fuel (.grid u ℓ), x.free = false
  | 0, u, ℓ => by simp [walkB]
  | f + 1, u, ℓ => by
    intro x hx
    have hnext : ∀ e, next R B e = .grid e (Pool.P0057.canon R B e) := fun e => by
      unfold next; rw [if_pos (by rw [hB1]; exact one_dvd e)]
    simp only [walkB] at hx
    by_cases hT : T ≤ u
    · rw [if_pos hT] at hx; simp at hx
    rw [if_neg hT] at hx
    have hrec : ∀ e, ∀ x ∈ walkB R T B t g f (next R B e), x.free = false := fun e x hx => by
      rw [hnext] at hx; exact walkB_grid_free hB1 f _ _ x hx
    rcases ht : t u ℓ with e | ⟨e, j⟩ | _ <;> rw [ht] at hx <;> simp only at hx
    · rcases List.mem_cons.1 hx with rfl | hx; exacts [rfl, hrec _ x hx]
    · rcases List.mem_cons.1 hx with rfl | hx; exacts [rfl, hrec _ x hx]
    · by_cases hl : ℓ + 1 < R
      · rw [if_pos hl] at hx; exact walkB_grid_free hB1 f _ _ x hx
      · rw [if_neg hl] at hx
        rcases List.mem_cons.1 hx with rfl | hx; exacts [rfl, hrec _ x hx]

end NoFree

section Cert

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E : ι → ℕ} {thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}
  {upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {aux0 : Finset ι}
  {U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {A0 : ι → Finset ι}
  {T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}

variable (E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ) in
/-- The data of the record of copy `c`: the actual run's if `c` is sampled, its own forced run's otherwise. -/
noncomputable def recD (c : ι) : ι → ℕ → ℝ :=
  if ωs c = true then gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ
  else fChat E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c

variable (E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) in
/-- `f` is in the actual run's start pools at every unit of `[s, s')`. -/
def PresA (f : ι) (s s' : ℕ) : Prop :=
  ∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
    (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).pools r ℓ

variable (E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) in
/-- **Active presence**: in the actual start pools and NOT retired (not in `aux`) at every unit of `[s, s')`. -/
def PresAct (f : ι) (s s' : ℕ) : Prop :=
  PresA E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f s s' ∧
    ∀ u, s ≤ u → u < s' → f ∉ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux

variable (E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ) in
/-- The retired set of the record's run of `c` (actual if sampled, forced otherwise) at unit `u`. -/
noncomputable def recAux (c : ι) (u : ℕ) : Finset ι :=
  if ωs c = true then (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux
  else (fRun E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c u).aux
/-- **Per-piece bound for a member that may retire at `r`** (P0160's `piece_of_retire` with the fake data only
required to dominate the base meta-arm's drawn losses, `drawn u ≤ d u f`, on the retired part). -/
theorem piece_split {κ : Type*} {f : κ} (r s s' : ℕ) (hss : s ≤ s') (ℓ c d : ℕ → κ → ℝ) (A V cB drawn : ℕ → ℝ)
    {α Γ W : ℝ}
    (hL : ∑ u ∈ Ico s (min s' (max s r)), A u ≤ ∑ u ∈ Ico s (min s' (max s r)), c u f + α +
      ∑ u ∈ Ico s (min s' (max s r)), V u)
    (hIX : ∑ u ∈ Ico s (min s' (max s r)), c u f ≤ ∑ u ∈ Ico s (min s' (max s r)), ℓ u f + Γ)
    (hlo : ∑ u ∈ Ico s (min s' (max s r)), ℓ u f ≤ ∑ u ∈ Ico s (min s' (max s r)), d u f + W)
    (hLB : ∑ u ∈ Ico (min s' (max s r)) s', A u ≤ ∑ u ∈ Ico (min s' (max s r)) s', cB u + α +
      ∑ u ∈ Ico (min s' (max s r)) s', V u)
    (hIXB : ∑ u ∈ Ico (min s' (max s r)) s', cB u ≤ ∑ u ∈ Ico (min s' (max s r)) s', drawn u + Γ)
    (hdr : ∀ u, r ≤ u → u < s' → drawn u ≤ d u f) :
    ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', d u f + (2 * α + 2 * Γ + W) + ∑ u ∈ Ico s s', V u := by
  have hm1 : s ≤ min s' (max s r) := le_min hss (le_max_left _ _)
  have hm2 : min s' (max s r) ≤ s' := min_le_left _ _
  have hd : ∑ u ∈ Ico (min s' (max s r)) s', drawn u ≤ ∑ u ∈ Ico (min s' (max s r)) s', d u f := by
    refine Finset.sum_le_sum fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := Finset.mem_Ico.1 hu
    refine hdr u ?_ hu2
    rcases le_total s' (max s r) with h | h
    · rw [min_eq_left h] at hu1; omega
    · rw [min_eq_right h] at hu1; exact (le_max_right s r).trans hu1
  rw [← Finset.sum_Ico_consecutive _ hm1 hm2, ← Finset.sum_Ico_consecutive _ hm1 hm2,
    ← Finset.sum_Ico_consecutive _ hm1 hm2]
  linarith
lemma aux_mono_le (haux : ∀ u, (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux ⊆
      (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ (u + 1)).aux) {a b : ℕ} (hab : a ≤ b) :
    (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).aux ⊆ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ b).aux := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (haux b)

variable (E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) in
/-- **The per-run hypotheses** (inputs, none discharged here): learner/IX/slot lower tail on ACTIVE presence only
(`hL`, `hIX`, `hlo`); base meta-arm, its IX, draw and base widths, `Σ Atrue ≤ Σ A + Ψ` on every interval; fake data
of retired copies ≥ the meta-arm's drawn losses (`hfake`); retirement monotone (`haux`). -/
structure ActHyp (ℓ cI : ℕ → ι → ℝ) (A Atrue V cB drawn bpol Bhat : ℕ → ℝ) (α Γ Ψ : ℝ) (W WD WB : ℕ → ℝ) :
    Prop where
  hL : ∀ f s s', s ≤ s' → PresAct E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f s s' →
    ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', cI u f + α + ∑ u ∈ Ico s s', V u
  hIX : ∀ f s s', s ≤ s' → PresAct E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f s s' →
    ∑ u ∈ Ico s s', cI u f ≤ ∑ u ∈ Ico s s', ℓ u f + Γ
  hlo : ∀ f s s', s ≤ s' → PresAct E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f s s' →
    ∑ u ∈ Ico s s', ℓ u f ≤
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) u f + W (s' - s)
  hLB : ∀ s s', s ≤ s' → ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', cB u + α + ∑ u ∈ Ico s s', V u
  hIXB : ∀ s s', s ≤ s' → ∑ u ∈ Ico s s', cB u ≤ ∑ u ∈ Ico s s', drawn u + Γ
  hDr : ∀ s s', s ≤ s' → ∑ u ∈ Ico s s', drawn u ≤ ∑ u ∈ Ico s s', bpol u + WD (s' - s)
  hBh : ∀ s s', s ≤ s' → ∑ u ∈ Ico s s', bpol u ≤ ∑ u ∈ Ico s s', Bhat u + WB (s' - s)
  htrue : ∀ s s', s ≤ s' → ∑ u ∈ Ico s s', Atrue u ≤ ∑ u ∈ Ico s s', A u + Ψ
  hfake : ∀ f u, f ∈ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux →
    drawn u ≤ Pool.P0105.incrOf (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) u f
  haux : ∀ u, (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux ⊆
    (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ (u + 1)).aux

open Pool.P0105 in
/-- **Per-piece bound for an actually present member**, active or retired (P0160's split at its first retirement:
active part by `hL`/`hIX`/`hlo`, retired part by `hLB`/`hIXB`/`hfake`). -/
theorem piece_of_presA {ℓ cI : ℕ → ι → ℝ} {A Atrue V cB drawn bpol Bhat : ℕ → ℝ} {α Γ Ψ : ℝ}
    {W WD WB : ℕ → ℝ}
    (H : ActHyp E thr0 θ R K D Lv Bt lev upd aux0 ωs φ ℓ cI A Atrue V cB drawn bpol Bhat α Γ Ψ W WD WB)
    (hWm : Monotone W) {f : ι} {s s' : ℕ} (hss : s ≤ s') (hP : PresA E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f s s') :
    ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', incrOf (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) u f +
      (2 * α + 2 * Γ + W (s' - s)) + ∑ u ∈ Ico s s', V u := by
  classical
  set Ax := fun u => (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux with hAx
  set r : ℕ := if h : ∃ u, s ≤ u ∧ u < s' ∧ f ∈ Ax u then Nat.find h else s' with hr
  have hsr : s ≤ r := by
    rw [hr]; split_ifs with h
    · exact (Nat.find_spec h).1
    · exact hss
  have hrs : r ≤ s' := by
    rw [hr]; split_ifs with h
    · exact (Nat.find_spec h).2.1.le
    · exact le_rfl
  have hm : min s' (max s r) = r := by rw [max_eq_right hsr, min_eq_right hrs]
  have hact : ∀ u, s ≤ u → u < r → f ∉ Ax u := by
    intro u h1 h2 hu
    rw [hr] at h2; split_ifs at h2 with h
    · exact Nat.find_min h h2 ⟨h1, by have := (Nat.find_spec h).2.1; omega, hu⟩
    · exact h ⟨u, h1, h2, hu⟩
  have hret : ∀ u, r ≤ u → u < s' → f ∈ Ax u := by
    intro u h1 h2
    by_cases h : ∃ u, s ≤ u ∧ u < s' ∧ f ∈ Ax u
    · have hrf : r = Nat.find h := by rw [hr, dif_pos h]
      have hin := (Nat.find_spec h).2.2
      rw [← hrf] at hin
      exact aux_mono_le H.haux h1 hin
    · have : r = s' := by rw [hr, dif_neg h]
      omega
  have hPA : PresAct E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f s r :=
    ⟨fun u h1 h2 => hP u h1 (by omega), fun u h1 h2 => hact u h1 h2⟩
  have hW : W (r - s) ≤ W (s' - s) := hWm (by omega)
  have h := piece_split (f := f) r s s' hss ℓ cI (incrOf (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ)) A V cB
    drawn (α := α) (Γ := Γ) (W := W (s' - s))
    (by rw [hm]; exact H.hL f s r hsr hPA) (by rw [hm]; exact H.hIX f s r hsr hPA)
    (by rw [hm]; exact (H.hlo f s r hsr hPA).trans (by linarith))
    (by rw [hm]; exact H.hLB r s' hrs) (by rw [hm]; exact H.hIXB r s' hrs)
    (fun u h1 h2 => H.hfake f u (hret u h1 h2))
  exact h
/-- Coupling of an unsampled copy's forced run with the actual run (e.g. P0176's `dz_forced_erase` + `dz_free_eq`):
pools differ only by the copy, data agree off the copy. -/
def Coup (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ)
    (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι) (aux0 : Finset ι)
    (U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι) (A0 : ι → Finset ι)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : Prop :=
  ∀ a, (∀ r ℓ, ((fRun E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c a).pools r ℓ).erase c =
      (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).pools r ℓ) ∧
    ∀ x, x ≠ c → ∀ t, (fRun E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c a).est x t =
      (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).est x t
lemma fChat_eq_of_coup {c : ι} (hc : Coup E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c) {x : ι} (hx : x ≠ c) :
    fChat E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c x = gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x := by
  funext t
  exact (hc t).2 x hx t
lemma gChat_zero (x : ι) : gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x 0 = 0 := rfl
/-- Presence propagates back to the entry: a copy in the actual start pools at `x` is there at every `u ∈ [E f, x]`. -/
lemma presA_of_start (hD : 0 < D) {f : ι} {x : ℕ}
    (h : ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs x (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x).pools r ℓ)
    {s s' : ℕ} (hs : E f ≤ s) (hs' : s' ≤ x + 1) : PresA E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f s s' := by
  intro u h1 h2
  have h' : ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs x (tpools E thr0 (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ)
      θ R K D Lv Bt lev ωs φ x) r ℓ := by rw [← gRun_pools_eq]; exact h
  have := Pool.P0074.present_back (C := gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) (θ := θ) (R := R) (lev := lev)
    hD (x - u) x u (by omega) (by omega) h'
  rw [← gRun_pools_eq] at this
  exact this
/-- The actual-run presence of a sampled copy that is never removed before `T`. -/
lemma presA_alive (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι} (hs : ωs c = true)
    (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c)
    (hrem : aRem E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = none) :
    PresA E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c (E c) T := by
  classical
  intro u h1 h2
  rw [gRun_pools_eq]
  rcases h1.lt_or_eq with hlt | rfl
  · have hal : Alive E thr0 (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) θ R K D Lv Bt lev ωs φ u c := by
      unfold aRem at hrem
      split_ifs at hrem with hh
      push Not at hh
      have := hh u hlt h2.le
      rw [gRun_pools_eq] at this
      exact this
    exact salive_of_alive hD hLv hlev hal
  · exact salive_entry hD hLv hs hthr hent
lemma aRet_le {c : ι} {u : ℕ} (h1 : E c < u) (h2 : u ≤ T)
    (hu : c ∈ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux) :
    ∃ e0, aRet E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e0 ∧ e0 ≤ u := by
  classical
  have h : ∃ y, E c < y ∧ y ≤ T ∧ c ∈ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ y).aux := ⟨u, h1, h2, hu⟩
  refine ⟨Nat.find h, ?_, Nat.find_min' h ⟨h1, h2, hu⟩⟩
  unfold aRet; rw [dif_pos h]

open Pool.P0105 in
/-- **Covered-record certificate of the mixed outcomes.** A comparator copy with mixed outcome `cov e` costs at most
`θ + R(2α + 2Γ + W) + W + Ψ + Σ V` on `[E c, e)` (`W` at the record length), under `ActHyp` (learner hypotheses on
ACTIVE members only; retired chain pieces through the base meta-arm), the upper tail of the record's data while its
copy is active (`hup`), and for an unsampled copy the coupling (`hcoup`). Via P0160's `cover_cert_ret`. -/
theorem cov_cert_mix (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι} (hthr : thr0 c < D)
    (hent : Bt (thr0 c) ∣ E c) (hcT : E c ≤ T)
    (hcoup : ωs c = false → Coup E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c)
    {ℓ cI : ℕ → ι → ℝ} {A Atrue V cB drawn bpol Bhat : ℕ → ℝ} {α Γ Ψ : ℝ} {W WD WB : ℕ → ℝ}
    (H : ActHyp E thr0 θ R K D Lv Bt lev upd aux0 ωs φ ℓ cI A Atrue V cB drawn bpol Bhat α Γ Ψ W WD WB)
    (hα : 0 ≤ α) (hΓ : 0 ≤ Γ) (hW0 : ∀ n, 0 ≤ W n) (hWm : Monotone W) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R)
    (hup : ∀ e, E c ≤ e → e ≤ T →
      (∀ u, E c < u → u < e → c ∉ recAux E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c u) →
      ∑ u ∈ Ico (E c) e, incrOf (recD E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c) u c ≤
        ∑ u ∈ Ico (E c) e, ℓ u c + W (e - E c))
    {e : ℕ} (h : outMix E thr0 θ R K D Lv Bt lev upd aux0 U A0 (D - 1) T ωs φ c = .cov e) :
    E c ≤ e ∧ e ≤ T ∧ ∑ u ∈ Ico (E c) e, (Atrue u - ℓ u c) ≤
      θ + R * (2 * α + 2 * Γ + W (e - E c)) + W (e - E c) + Ψ + ∑ u ∈ Ico (E c) e, V u := by
  classical
  set CA := gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ with hCA
  have hWl : ∀ s s', E c ≤ s → s' ≤ e → W (s' - s) ≤ W (e - E c) := fun s s' h1 h2 => hWm (by omega)
  have hβ : (0 : ℝ) ≤ 2 * α + 2 * Γ + W (e - E c) := by have := hW0 (e - E c); positivity
  have hpieceA : ∀ f s s', s ≤ s' → PresA E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f s s' → E c ≤ s → s' ≤ e →
      ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', incrOf CA u f + (2 * α + 2 * Γ + W (e - E c)) +
        ∑ u ∈ Ico s s', V u := by
    intro f s s' hss hP h1 h2
    have := piece_of_presA H hWm hss hP
    linarith [hWl s s' h1 h2]
  unfold outMix at h
  split_ifs at h with hs
  · -- sampled: the actual run
    have hrec : recD E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c = CA := by simp [recD, hs, hCA]
    have hraux : ∀ u, recAux E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c u =
        (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux := fun u => by simp [recAux, hs]
    rcases outA_cov h with ⟨hev, hlt⟩ | ⟨heT, hrem, hret⟩
    · obtain ⟨hae, heT, -, x, hxe, hx1, hxs, hxn, -⟩ := aRem_spec hD hLv hlev hs hthr hent hev
      subst hxe
      obtain ⟨-, Q', hQ', y, -, hcF, hcov⟩ := covered_of_removed_tpools hD hLv hlev hxs hxn
      rw [← cumL_incrOf (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) (fun x => gChat_zero x)] at hcov
      have hact : ∀ u, E c < u → u < x + 1 → c ∉ recAux E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c u := by
        intro u h1 h2 hu
        rw [hraux] at hu
        obtain ⟨e0, he0, hle⟩ := aRet_le (T := T) h1 (by omega) hu
        have := hlt e0 he0
        omega
      have hc := Pool.P0160.cover_cert_ret E (x + 1) ℓ (incrOf CA) A Atrue V hβ
        (fun f => PresA E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f (max (E c) (E f)) (x + 1))
        (fun f hP s s' h1 h2 h3 h4 => hpieceA f s s' h3 (fun u hu1 hu2 => hP u (by omega) (by omega)) h1 h4)
        (fun f hf => by
          obtain ⟨j, hj⟩ := hQ' f (Finset.mem_filter.1 hf).1
          refine presA_of_start hD (x := x) ⟨curT E thr0 D Bt c x, j, ?_⟩ (le_max_right _ _) le_rfl
          rw [gRun_pools_eq]; exact hj)
        hcov (by have := hup (x + 1) (by omega) heT hact; rw [hrec] at this; exact this)
        (H.htrue _ _ (by omega))
      exact ⟨by omega, heT, by linarith⟩
    · subst heT
      have hnr : ∀ u, E c ≤ u → u < e → c ∉ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ u).aux := by
        intro u h1 h2 hu
        have hu' : c ∈ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ (u + 1)).aux := H.haux u hu
        obtain ⟨e0, he0, -⟩ := aRet_le (T := e) (show E c < u + 1 by omega) (by omega) hu'
        rw [hret] at he0; cases he0
      have hP : PresAct E thr0 θ R K D Lv Bt lev upd aux0 ωs φ c (E c) e :=
        ⟨presA_alive hD hLv hlev hs hthr hent hrem, hnr⟩
      have h1 := H.hL c (E c) e (by omega) hP
      have h2 := H.hIX c (E c) e (by omega) hP
      have h3 := H.htrue (E c) e (by omega)
      have hW := hW0 (e - E c)
      have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
      have hRm : 2 * α + 2 * Γ + W (e - E c) ≤ R * (2 * α + 2 * Γ + W (e - E c)) := by nlinarith
      rw [Finset.sum_sub_distrib]
      refine ⟨by omega, le_rfl, by linarith⟩
  · -- unsampled: the forced run, coupled with the actual run
    have hs' : ωs c = false := by simpa using hs
    have hcp := hcoup hs'
    have hrec : recD E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c =
        fChat E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c := by simp [recD, hs]
    have hraux : ∀ u, recAux E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c u =
        (fRun E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c u).aux := fun u => by simp [recAux, hs]
    obtain ⟨hae, heT, hnot, -, x, hxe, -, Q', hQ', y, -, hcF, hcov⟩ := cov_certZ hD hLv hlev hthr hent h
    subst hxe
    set CF := fChat E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c with hCF
    rw [← cumL_incrOf CF (fun _ => rfl)] at hcov
    have hFne : ∀ f ∈ Fof Q' y, f ≠ c := fun f hf hfc => hcF (hfc ▸ hf)
    have hinc : ∀ f, f ≠ c → ∀ u, incrOf CF u f = incrOf CA u f := by
      intro f hf u; unfold incrOf; rw [hCF, fChat_eq_of_coup hcp hf]
    have hact : ∀ u, E c < u → u < x + 1 → c ∉ recAux E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c u := by
      intro u h1 h2; rw [hraux]; exact hnot u h1 (by omega)
    have hc := Pool.P0160.cover_cert_ret E (x + 1) ℓ (incrOf CF) A Atrue V hβ
      (fun f => f ≠ c ∧ PresA E thr0 θ R K D Lv Bt lev upd aux0 ωs φ f (max (E c) (E f)) (x + 1))
      (fun f hP s s' h1 h2 h3 h4 => by
        rw [Finset.sum_congr rfl fun u _ => hinc f hP.1 u]
        exact hpieceA f s s' h3 (fun u hu1 hu2 => hP.2 u (by omega) (by omega)) h1 h4)
      (fun f hf => by
        refine ⟨hFne f hf, ?_⟩
        obtain ⟨j, hj⟩ := hQ' f (Finset.mem_filter.1 hf).1
        refine presA_of_start hD (x := x) ⟨curT E thr0 D Bt c x, j, ?_⟩ (le_max_right _ _) le_rfl
        have hfe : f ∈ (startPools E thr0 D Lv Bt (forceS ωs c) x
            (fRun E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c x).pools (curT E thr0 D Bt c x) j).erase c :=
          Finset.mem_erase.2 ⟨hFne f hf, hj⟩
        rw [startPools_erase c (forceS ωs c) ωs (fun z hz => by simp [forceS, Function.update_of_ne hz]) hs'] at hfe
        rwa [show (fun r ℓ => ((fRun E thr0 θ R K D Lv Bt lev (U c) (A0 c) ωs φ c x).pools r ℓ).erase c) =
            (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x).pools from funext fun r => funext fun ℓ => (hcp x).1 r ℓ]
          at hfe)
      hcov (by have := hup (x + 1) (by omega) heT hact; rw [hrec] at this; exact this)
      (H.htrue _ _ (by omega))
    exact ⟨by omega, heT, by linarith⟩

variable (E thr0 θ R K D Lv Bt lev upd aux0 U A0 T ωs φ) in
/-- The record's run retires `c` first at `e`: the actual run for a sampled copy, its forced run otherwise. -/
def RetAt (c : ι) (e : ℕ) : Prop :=
  if ωs c = true then aRet E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e
  else retT E thr0 θ R K D Lv Bt lev (U c) (A0 c) T ωs φ c = some e
lemma outMix_bev {c : ι} {e j : ℕ}
    (h : outMix E thr0 θ R K D Lv Bt lev upd aux0 U A0 (D - 1) T ωs φ c = .bev e j) :
    RetAt E thr0 θ R K D Lv Bt lev upd aux0 U A0 T ωs φ c e ∧ E c < e ∧ e ≤ T ∧
      j = min (curT E thr0 D Bt c e) (D - 1) := by
  unfold outMix at h
  unfold RetAt
  split_ifs at h ⊢ with hs
  · obtain ⟨hr, hj, -⟩ := outA_bev h
    obtain ⟨h1, h2, -⟩ := aRet_spec hr
    exact ⟨hr, h1, h2, hj⟩
  · obtain ⟨hr, hj, -⟩ := outZ_bev h
    obtain ⟨h1, h2, -⟩ := retT_spec hr
    exact ⟨hr, h1, h2, hj⟩

open Pool.P0105 in
/-- **(b″)-record certificate of the mixed outcomes** (P0148's `bend_cert`): a copy with mixed outcome `bev e j` costs
at most `Ψ + α + Σ V + Γ + W_D + W_B + W − Λ j (e − E c)` on `[E c, e)`, under `ActHyp` (base meta-arm part), the
rule's margin (`hrule`) and the upper tail of the record's data while its copy is active (`hup`). -/
theorem bev_cert_mix {c : ι} {ℓ cI : ℕ → ι → ℝ} {A Atrue V cB drawn bpol Bhat : ℕ → ℝ} {α Γ Ψ : ℝ}
    {W WD WB : ℕ → ℝ} (Λ : ℕ → ℕ → ℝ)
    (H : ActHyp E thr0 θ R K D Lv Bt lev upd aux0 ωs φ ℓ cI A Atrue V cB drawn bpol Bhat α Γ Ψ W WD WB)
    (hrule : ∀ e, RetAt E thr0 θ R K D Lv Bt lev upd aux0 U A0 T ωs φ c e →
      Λ (min (curT E thr0 D Bt c e) (D - 1)) (e - E c) ≤
        ∑ u ∈ Ico (E c) e, incrOf (recD E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c) u c -
          ∑ u ∈ Ico (E c) e, Bhat u)
    (hup : ∀ e, E c ≤ e → e ≤ T →
      (∀ u, E c < u → u < e → c ∉ recAux E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c u) →
      ∑ u ∈ Ico (E c) e, incrOf (recD E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c) u c ≤
        ∑ u ∈ Ico (E c) e, ℓ u c + W (e - E c))
    {e j : ℕ} (h : outMix E thr0 θ R K D Lv Bt lev upd aux0 U A0 (D - 1) T ωs φ c = .bev e j) :
    E c < e ∧ e ≤ T ∧ ∑ u ∈ Ico (E c) e, (Atrue u - ℓ u c) ≤
      Ψ + α + ∑ u ∈ Ico (E c) e, V u + Γ + WD (e - E c) + WB (e - E c) + W (e - E c) - Λ j (e - E c) := by
  obtain ⟨hr, h1, h2, rfl⟩ := outMix_bev h
  have hact : ∀ u, E c < u → u < e → c ∉ recAux E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c u := by
    intro u hu1 hu2
    unfold RetAt at hr
    unfold recAux
    split_ifs at hr ⊢
    · exact (aRet_spec hr).2.2.2 u hu1 hu2
    · exact (retT_spec hr).2.2.2 u hu1 hu2
  refine ⟨h1, h2, ?_⟩
  exact Pool.P0148.bend_cert (E c) e A Atrue V cB drawn bpol Bhat
    (fun u => incrOf (recD E thr0 θ R K D Lv Bt lev upd aux0 U A0 ωs φ c) u c) (fun u => ℓ u c)
    (H.hLB _ _ h1.le) (H.hIXB _ _ h1.le) (H.hDr _ _ h1.le) (H.hBh _ _ h1.le) (hrule e hr) (hup e h1.le h2 hact)
    (H.htrue _ _ h1.le)

end Cert

end Pool.P0186
