import Pool.P0194.Proc
import Pool.P0191.DZConc

/-!
# Slot-data concentration for P0194's round-level per-thread process

P0191 proves interval-uniform concentration of `dzRun`'s slot data over P0191's own unit coins, for a FIXED retirement
rule. P0194's process runs `dzRun` with `B = 1` on its ROUND coins `RC P` (law `wR`: round kind × ALG draw × BASE's
coins), and its retirement rule `rhD` reads BASE's estimate `B̂`, which depends on the coins. Here the concentration is
proved directly on P0194's coins, with the gate read from the coin prefix (so any coin-dependent retirement is
allowed):

* `nuD`: the round-coin law as a PMF (under `ParD.IsLaw`, `N > 0`); `extD`: a coin prefix extended by a default coin.
* `slotEst`: copy `c`'s slot estimate at round `u` (`ℓ/x_j` when the round draws `c`'s slot of thread `j`, else `0`);
  `gateS`: `c` is active (start-pool member, not retired) and every thread fits; `DS`: the gated error
  `slotEst − ℓ`; `rS = 1/x_{curT}` (P0191's `rC` with `B = 1`).
* `sum_wR_kind`: marginalization of `wR` to round kinds.
* **`incrV_DS`**: P0158's `IncrV` with range and variance `1/x_{curT}`, and `DS ≥ −1`.
* **`prob_not_goodDS`** / **`prob_not_goodDS_all`**: with probability `≥ 1 − |ι|·2(T+1)²e^{−L}` over P0194's round
  coins, for every copy and every interval `[a, b) ⊆ [0, T)`, the gated sum of `slotEst − ℓ` is
  `< 2√(L·Σ_{[a,b)} 1/x_{curT}) + 2·max(1, max_{[a,b)} 1/x_{curT})·L` in absolute value.
* **`slotEst_eq_inc`**: identification with the run: for an active copy, `slotEst` is the increment of P0194's pool data
  (P0156's `gChat`) at round `u`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0156 Pool.P0065 Pool.P0095

namespace Pool.P0203

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι)

/-- The round-coin law as a PMF. -/
noncomputable def nuD (hL : P.IsLaw) (hN : 0 < P.N) : PMF (RC P) :=
  PMF.ofFintype (fun rc => ENNReal.ofReal (wR P rc)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun rc _ => wR_nonneg P hL rc), sum_wR P hL hN, ENNReal.ofReal_one])

theorem nuD_toReal (hL : P.IsLaw) (hN : 0 < P.N) (rc : RC P) : (nuD P hL hN rc).toReal = wR P rc := by
  simp [nuD, ENNReal.toReal_ofReal (wR_nonneg P hL rc)]

/-- A finite coin prefix extended by a default coin. -/
def extD (rc0 : RC P) {t : ℕ} (ω : Fin t → RC P) : ℕ → RC P :=
  fun u => if h : u < t then ω ⟨u, h⟩ else rc0

theorem extD_snoc_agree (rc0 : RC P) {t : ℕ} (ω : Fin t → RC P) (z : RC P) :
    Agree P (extD P rc0 (Fin.snoc ω z : Fin (t + 1) → RC P)) (extD P rc0 ω) t := by
  intro v hv
  simp only [extD, dif_pos hv, dif_pos (by omega : v < t + 1)]
  simp [Fin.snoc, hv]

theorem extD_snoc_last (rc0 : RC P) {t : ℕ} (ω : Fin t → RC P) (z : RC P) :
    extD P rc0 (Fin.snoc ω z : Fin (t + 1) → RC P) t = z := by
  simp [extD, Fin.snoc]

theorem extD_init_agree (rc0 : RC P) {t : ℕ} (ω : Fin (t + 1) → RC P) :
    Agree P (extD P rc0 ω) (extD P rc0 (Fin.init ω)) t := by
  intro v hv
  simp only [extD, dif_pos hv, dif_pos (by omega : v < t + 1)]
  rfl

/-- Weight of a slot-or-exploitation kind is P0176's round weight with `w0 = wE`. -/
theorem wK_some (r : RT P.D P.sl) : wK P (some r) = wRT P.sl P.xr P.wE r := by
  rcases r with _ | ⟨j, k⟩ <;> rfl

/-- **Marginalization to round kinds.** -/
theorem sum_wR_kind (hN : 0 < P.N) (G : Kd P → ℝ) :
    ∑ rc : RC P, wR P rc * G rc.1 = ∑ κ : Kd P, wK P κ * G κ := by
  have hμ : ∑ yB : P.AB.Y, (P.AB.μ yB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.μ
  have hν : ∑ zB : P.AB.Z, (P.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.ν
  have hN' : (0 : ℝ) < P.N := by exact_mod_cast hN
  simp only [Fintype.sum_prod_type, wR]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have : ∀ d : Fin P.N, ∑ yB : P.AB.Y, ∑ zB : P.AB.Z,
      wK P κ * (1 / (P.N : ℝ)) * (P.AB.μ yB).toReal * (P.AB.ν zB).toReal * G κ =
      wK P κ * (1 / (P.N : ℝ)) * G κ := by
    intro d
    have e : ∀ yB zB, wK P κ * (1 / (P.N : ℝ)) * (P.AB.μ yB).toReal * (P.AB.ν zB).toReal * G κ =
        (wK P κ * (1 / (P.N : ℝ)) * G κ) * ((P.AB.μ yB).toReal * (P.AB.ν zB).toReal) := fun _ _ => by ring
    simp only [e, ← Finset.mul_sum, hν, hμ, mul_one]
  rw [Finset.sum_congr rfl fun d _ => this d, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- A sum over round kinds: the BASE kind plus P0176's round types with `w0 = wE`. -/
theorem sum_wK_split (G : Kd P → ℝ) :
    ∑ κ : Kd P, wK P κ * G κ = P.wB * G none + ∑ r : RT P.D P.sl, wRT P.sl P.xr P.wE r * G (some r) := by
  rw [Fintype.sum_option]
  simp only [wK_some]
  rfl

variable (ℓ : LossSeq n) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (rc0 : RC P)

/-- Copy `c`'s slot estimate at round `u` (P0176's `dzC` with `B = 1`). -/
noncomputable def slotEst (ω : ℕ → RC P) (u : ℕ) (c : ι) : ℝ :=
  dzC P.D 1 P.xr (ℓr P ℓ) u c 0 (obsR P.D P.Lv P.sl P.lay (sp P ℓ ω ωs φ u) ((ω u).1.getD none))

open Classical in
/-- The gate: `c` is active at round `u` (start-pool member, not retired) and every thread fits. -/
noncomputable def gateS (c : ι) (u : ℕ) (ω : Fin u → RC P) : Bool :=
  decide (c ∈ active P ℓ (extD P rc0 ω) ωs φ u ∧ Fits P.Lv P.sl (sp P ℓ (extD P rc0 ω) ωs φ u))

/-- The gated slot error of copy `c` at round `u`. -/
noncomputable def DS (c : ι) (u : ℕ) (ω : Fin (u + 1) → RC P) : ℝ :=
  if gateS P ℓ ωs φ rc0 c u (Fin.init ω) then slotEst P ℓ ωs φ (extD P rc0 ω) u c - ℓr P ℓ u c else 0

/-- The range and variance proxy: `1/x` at the copy's current thread (P0191's `rC` with `B = 1`). -/
noncomputable def rS (c : ι) (u : ℕ) : ℝ := Pool.P0191.rC 1 P.xr P.E P.thr0 P.Bt c u

theorem ℓr_mem (u : ℕ) (x : ι) : 0 ≤ ℓr P ℓ u x ∧ ℓr P ℓ u x ≤ 1 := by
  unfold ℓr; cases ℓ u (P.arm x) <;> simp

/-- The facts at an active round. -/
theorem act_facts (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (c : ι) (u : ℕ)
    (W : ℕ → RC P) (hm : c ∈ members P.D P.Lv (sp P ℓ W ωs φ u)) :
    ∃ h : curT P.E P.thr0 P.D P.Bt c u < P.D,
      c ∈ blockMem P.Lv (sp P ℓ W ωs φ u) ((⟨curT P.E P.thr0 P.D P.Bt c u, h⟩ : Fin P.D) : ℕ) ∧
      ∀ j : Fin P.D, j ≠ ⟨curT P.E P.thr0 P.D P.Bt c u, h⟩ → c ∉ blockMem P.Lv (sp P ℓ W ωs φ u) j := by
  simp only [members, Finset.mem_biUnion, Finset.mem_range] at hm
  obtain ⟨r, hr, l, hl, hc⟩ := hm
  obtain ⟨hrc, hrD⟩ := Pool.P0191.start_loc P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev hD hLv hlev _ _ ωs φ u hc
  subst hrc
  refine ⟨hrD, ?_, fun j hj hcj => hj ?_⟩
  · simp only [blockMem, Finset.mem_biUnion, Finset.mem_range]; exact ⟨l, hl, hc⟩
  · simp only [blockMem, Finset.mem_biUnion, Finset.mem_range] at hcj
    obtain ⟨l', hl', hc'⟩ := hcj
    have := (Pool.P0191.start_loc P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev hD hLv hlev _ _ ωs φ u hc').1
    exact Fin.ext this

/-- On a snoc'ed prefix, the slot estimate reads the start pools of the prefix and the new coin's kind. -/
theorem slotEst_snoc {u : ℕ} (ω : Fin u → RC P) (rc : RC P) (c : ι) :
    slotEst P ℓ ωs φ (extD P rc0 (Fin.snoc ω rc : Fin (u + 1) → RC P)) u c =
      dzC P.D 1 P.xr (ℓr P ℓ) u c 0
        (obsR P.D P.Lv P.sl P.lay (sp P ℓ (extD P rc0 ω) ωs φ u) (rc.1.getD none)) := by
  unfold slotEst
  rw [sp_congr ωs φ u (extD_snoc_agree P rc0 ω rc), extD_snoc_last]

open Classical in
/-- **P0158's hypotheses** for the gated slot error of every copy: increments `≤ 1/x_{curT}`, centred, with second
moment `≤ 1/x_{curT}`, and `≥ −1 ≥ −1/x_{curT}` (rates `≤ 1`). -/
theorem incrV_DS (hL : P.IsLaw) (hN : 0 < P.N) (hD : 0 < P.D) (hLv : 0 < P.Lv)
    (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j)
    (hxr1 : ∀ j, P.xr j ≤ 1) (c : ι) :
    Pool.P0158.IncrV (nuD P hL hN) (DS P ℓ ωs φ rc0 c) (rS P c) (rS P c) ∧
      ∀ u (ω : Fin u → RC P) z, -rS P c u ≤ DS P ℓ ωs φ rc0 c u (Fin.snoc ω z) := by
  have hrS1 : ∀ u, 1 ≤ rS P c u := by
    intro u; unfold rS Pool.P0191.rC
    rw [Nat.cast_one, le_div_iff₀ (Pool.P0191.xrN_pos P.xr hxr _), one_mul]
    unfold Pool.P0191.xrN; split_ifs
    · exact hxr1 _
    · exact le_rfl
  -- the facts at a gated round
  have hact : ∀ u (ω : Fin u → RC P), gateS P ℓ ωs φ rc0 c u ω = true →
      ∃ h : curT P.E P.thr0 P.D P.Bt c u < P.D,
        rS P c u = 1 / P.xr ⟨curT P.E P.thr0 P.D P.Bt c u, h⟩ ∧
        c ∈ blockMem P.Lv (sp P ℓ (extD P rc0 ω) ωs φ u) ((⟨curT P.E P.thr0 P.D P.Bt c u, h⟩ : Fin P.D) : ℕ) ∧
        (∀ j : Fin P.D, j ≠ ⟨curT P.E P.thr0 P.D P.Bt c u, h⟩ →
          c ∉ blockMem P.Lv (sp P ℓ (extD P rc0 ω) ωs φ u) j) ∧
        Fits P.Lv P.sl (sp P ℓ (extD P rc0 ω) ωs φ u) := by
    intro u ω hg
    simp only [gateS, decide_eq_true_eq, active, Finset.mem_sdiff] at hg
    obtain ⟨⟨hm, _⟩, hfit⟩ := hg
    obtain ⟨h, hin, hout⟩ := act_facts P ℓ ωs φ hD hLv hlev c u _ hm
    refine ⟨h, ?_, hin, hout, hfit⟩
    simp [rS, Pool.P0191.rC, Pool.P0191.xrN, h]
  -- one round: mean and second moment of the slot estimate
  have hround : ∀ u (ω : Fin u → RC P) (h : curT P.E P.thr0 P.D P.Bt c u < P.D)
      (hin : c ∈ blockMem P.Lv (sp P ℓ (extD P rc0 ω) ωs φ u) ((⟨curT P.E P.thr0 P.D P.Bt c u, h⟩ : Fin P.D) : ℕ))
      (hout : ∀ j : Fin P.D, j ≠ ⟨curT P.E P.thr0 P.D P.Bt c u, h⟩ →
          c ∉ blockMem P.Lv (sp P ℓ (extD P rc0 ω) ωs φ u) j)
      (hfit : Fits P.Lv P.sl (sp P ℓ (extD P rc0 ω) ωs φ u)) (f : ℝ → ℝ) (hf : f 0 = 0),
      ∑ rc : RC P, wR P rc * f (dzC P.D 1 P.xr (ℓr P ℓ) u c 0
          (obsR P.D P.Lv P.sl P.lay (sp P ℓ (extD P rc0 ω) ωs φ u) (rc.1.getD none))) =
        P.xr ⟨curT P.E P.thr0 P.D P.Bt c u, h⟩ * f (ℓr P ℓ u c / P.xr ⟨curT P.E P.thr0 P.D P.Bt c u, h⟩) := by
    intro u ω h hin hout hfit f hf
    rw [sum_wR_kind P hN (fun κ => f (dzC P.D 1 P.xr (ℓr P ℓ) u c 0
      (obsR P.D P.Lv P.sl P.lay (sp P ℓ (extD P rc0 ω) ωs φ u) (κ.getD none)))), sum_wK_split]
    have hnone : dzC P.D 1 P.xr (ℓr P ℓ) u c 0
        (obsR P.D P.Lv P.sl P.lay (sp P ℓ (extD P rc0 ω) ωs φ u) ((none : Kd P).getD none)) = 0 := rfl
    simp only [hnone, hf, mul_zero, zero_add, Option.getD_some]
    have hm := Pool.P0191.round_mean P.Lv P.sl 1 P.xr (ℓr P ℓ) P.lay hlay P.wE (sp P ℓ (extD P rc0 ω) ωs φ u) u c 0
      _ hin hout (hfit _) (hxr _).ne' f hf
    simpa using hm
  refine ⟨⟨fun u ω z => ?_, fun u ω => ?_, fun u ω => ?_⟩, fun u ω z => ?_⟩
  · -- up
    simp only [DS, Fin.init_snoc]
    split_ifs with hg
    · obtain ⟨h, hr, hin, hout, hfit⟩ := hact u ω hg
      rw [slotEst_snoc, hr]
      have := (Pool.P0191.dzC_le P.Lv P.sl 1 P.xr (ℓr P ℓ) P.lay hlay hxr (fun u x => (ℓr_mem P ℓ u x).1)
        (fun u x => (ℓr_mem P ℓ u x).2) _ u c 0 _ hout (z.1.getD none)).2
      linarith [(ℓr_mem P ℓ u c).1]
    · linarith [hrS1 u]
  · -- mean
    simp only [DS, Fin.init_snoc, nuD_toReal]
    split_ifs with hg
    · obtain ⟨h, _, hin, hout, hfit⟩ := hact u ω hg
      simp only [slotEst_snoc, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_wR P hL hN, one_mul]
      have hm := hround u ω h hin hout hfit id rfl
      simp only [id] at hm
      have hx := (hxr ⟨curT P.E P.thr0 P.D P.Bt c u, h⟩).ne'
      rw [hm, mul_div_cancel₀ _ hx, sub_self]
    · simp
  · -- var
    simp only [DS, Fin.init_snoc, nuD_toReal]
    split_ifs with hg
    · obtain ⟨h, hr, hin, hout, hfit⟩ := hact u ω hg
      rw [hr]
      simp only [slotEst_snoc]
      have hm := hround u ω h hin hout hfit id rfl
      have hsq := hround u ω h hin hout hfit (fun v => v ^ 2) (by norm_num)
      simp only [id] at hm hsq
      set x := P.xr ⟨curT P.E P.thr0 P.D P.Bt c u, h⟩
      set l := ℓr P ℓ u c
      have e : ∀ rc : RC P, wR P rc * (dzC P.D 1 P.xr (ℓr P ℓ) u c 0
          (obsR P.D P.Lv P.sl P.lay (sp P ℓ (extD P rc0 ω) ωs φ u) (rc.1.getD none)) - l) ^ 2 =
          wR P rc * (dzC P.D 1 P.xr (ℓr P ℓ) u c 0
            (obsR P.D P.Lv P.sl P.lay (sp P ℓ (extD P rc0 ω) ωs φ u) (rc.1.getD none))) ^ 2 -
          2 * l * (wR P rc * dzC P.D 1 P.xr (ℓr P ℓ) u c 0
            (obsR P.D P.Lv P.sl P.lay (sp P ℓ (extD P rc0 ω) ωs φ u) (rc.1.getD none))) +
          l ^ 2 * wR P rc := fun rc => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsq, hm, sum_wR P hL hN]
      have hx0 : 0 < x := hxr _
      have hl0 : 0 ≤ l := (ℓr_mem P ℓ u c).1
      have hl1 : l ≤ 1 := (ℓr_mem P ℓ u c).2
      have e2 : x * (l / x) ^ 2 - 2 * l * (x * (l / x)) + l ^ 2 * 1 = l ^ 2 / x - l ^ 2 := by
        field_simp; ring
      rw [e2]
      have : l ^ 2 / x ≤ 1 / x := div_le_div_of_nonneg_right (by nlinarith) hx0.le
      nlinarith [sq_nonneg l]
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
      linarith [hrS1 u]
  · -- lower
    simp only [DS, Fin.init_snoc]
    split_ifs with hg
    · obtain ⟨h, _, hin, hout, hfit⟩ := hact u ω hg
      rw [slotEst_snoc]
      have := (Pool.P0191.dzC_le P.Lv P.sl 1 P.xr (ℓr P ℓ) P.lay hlay hxr (fun u x => (ℓr_mem P ℓ u x).1)
        (fun u x => (ℓr_mem P ℓ u x).2) _ u c 0 _ hout (z.1.getD none)).1
      linarith [(ℓr_mem P ℓ u c).2, hrS1 u]
    · linarith [hrS1 u]

open Classical in
/-- **Interval-uniform slot concentration on P0194's round coins, one copy.** -/
theorem prob_not_goodDS (hL : P.IsLaw) (hN : 0 < P.N) (hD : 0 < P.D) (hLv : 0 < P.Lv)
    (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j)
    (hxr1 : ∀ j, P.xr j ≤ 1) (c : ι) {L : ℝ} (hLp : 0 < L) (T : ℕ) :
    (∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω *
      if Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T ω
      then (0 : ℝ) else 1) ≤ 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
  obtain ⟨hI, hlow⟩ := incrV_DS P ℓ ωs φ rc0 hL hN hD hLv hlev hlay hxr hxr1 c
  have hrS0 : ∀ u, 0 ≤ rS P c u := fun u => Pool.P0191.rC_nonneg 1 P.xr P.E P.thr0 P.Bt hxr c u
  exact Pool.P0158.prob_not_goodV _ _ _ hI hlow hrS0 _ (fun a b => Pool.P0158.rmax1_pos _ a b)
    (fun a b s has hsb => Pool.P0158.le_rmax1 _ has hsb) hLp T

open Classical in
/-- **All copies at once**: failure probability `≤ |ι|·2(T+1)²e^{−L}`. -/
theorem prob_not_goodDS_all (hL : P.IsLaw) (hN : 0 < P.N) (hD : 0 < P.D) (hLv : 0 < P.Lv)
    (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j)
    (hxr1 : ∀ j, P.xr j ≤ 1) {L : ℝ} (hLp : 0 < L) (T : ℕ) :
    (∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω *
      if ∀ c, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T ω
      then (0 : ℝ) else 1) ≤ Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) := by
  have hw : ∀ ω : Fin T → RC P, 0 ≤ Pool.P0092.wgt (nuD P hL hN) ω :=
    fun ω => Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  set G : ι → (Fin T → RC P) → Prop := fun c ω =>
    Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T ω with hG
  calc _ ≤ ∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω * ∑ c : ι, (if G c ω then (0 : ℝ) else 1) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
        split_ifs with hall
        · exact Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num
        · push_neg at hall
          obtain ⟨c, hc⟩ := hall
          refine le_trans ?_ (Finset.single_le_sum (f := fun c => if G c ω then (0 : ℝ) else 1)
            (fun c _ => by split_ifs <;> norm_num) (Finset.mem_univ c))
          simp [hG, hc]
    _ = ∑ c : ι, ∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω * (if G c ω then (0 : ℝ) else 1) := by
        simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ _c : ι, 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := Finset.sum_le_sum fun c _ =>
        prob_not_goodDS P ℓ ωs φ rc0 hL hN hD hLv hlev hlay hxr hxr1 c hLp T
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Identification with the run.** For a copy not retired at round `u`, its data increment in P0194's pool (P0156's
`gChat`, the cover and rule-(b″) data) at round `u` is `slotEst`. -/
theorem slotEst_eq_inc (ω : ℕ → RC P) (u : ℕ) (c : ι) (hc : c ∉ (pool P ℓ ω ωs φ u).aux) :
    gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
        (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ c (u + 1) -
      gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
        (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ c u =
      slotEst P ℓ ωs φ ω u c := by
  rw [gChat_succ, add_sub_cancel_left]
  unfold gInc
  have hc' : c ∉ (gRun P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ u).aux := hc
  simp only [dzUpd, dzUpdO, dzIncO, if_neg hc', Fin.sum_univ_one, slotEst, sp, pool, zc]

/-! ### Transport: the prefix good event controls the run sums of a full coin sequence -/

/-- The length-`t` prefix of a full coin sequence. -/
def pre (ω : ℕ → RC P) (t : ℕ) : Fin t → RC P := fun i => ω i

theorem extD_pre_agree (ω : ℕ → RC P) (t : ℕ) : Agree P (extD P rc0 (pre P ω t)) ω t := by
  intro v hv
  simp [extD, pre, hv]

theorem init_pre (ω : ℕ → RC P) (t : ℕ) : Fin.init (pre P ω (t + 1)) = pre P ω t := by
  funext i; rfl

/-- The slot estimate at round `u` reads only the coins of rounds `≤ u`. -/
theorem slotEst_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' (u + 1)) (c : ι) :
    slotEst P ℓ ωs φ ω u c = slotEst P ℓ ωs φ ω' u c := by
  unfold slotEst
  rw [sp_congr ωs φ u (Agree.mono h (Nat.le_succ u)), h u (Nat.lt_succ_self u)]

open Classical in
/-- The gated increment of round `u` on the prefix of a full sequence `ω` is the run's own quantity: if `c` is active
and every thread fits at round `u` of the run on `ω`, the data increment (P0156's `gChat`) minus the loss, else `0`. -/
theorem DS_pre (ω : ℕ → RC P) (u : ℕ) (c : ι) :
    DS P ℓ ωs φ rc0 c u (pre P ω (u + 1)) =
      if c ∈ active P ℓ ω ωs φ u ∧ Fits P.Lv P.sl (sp P ℓ ω ωs φ u) then
        (gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ c (u + 1) -
          gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ c u) - ℓr P ℓ u c
      else 0 := by
  have hag : Agree P (extD P rc0 (pre P ω u)) ω u := extD_pre_agree P rc0 ω u
  have hact : active P ℓ (extD P rc0 (pre P ω u)) ωs φ u = active P ℓ ω ωs φ u := active_congr ωs φ u hag
  have hsp : sp P ℓ (extD P rc0 (pre P ω u)) ωs φ u = sp P ℓ ω ωs φ u := sp_congr ωs φ u hag
  have hgate : gateS P ℓ ωs φ rc0 c u (Fin.init (pre P ω (u + 1))) =
      decide (c ∈ active P ℓ ω ωs φ u ∧ Fits P.Lv P.sl (sp P ℓ ω ωs φ u)) := by
    rw [init_pre]; unfold gateS; rw [hact, hsp]
  unfold DS
  rw [hgate]
  by_cases hg : c ∈ active P ℓ ω ωs φ u ∧ Fits P.Lv P.sl (sp P ℓ ω ωs φ u)
  · rw [if_pos (decide_eq_true hg), if_pos hg]
    have hret : c ∉ (pool P ℓ ω ωs φ u).aux := by
      have := hg.1; simp only [active, Finset.mem_sdiff] at this; exact this.2
    rw [slotEst_eq_inc P ℓ ωs φ ω u c hret,
      slotEst_congr P ℓ ωs φ u (extD_pre_agree P rc0 ω (u + 1)) c]
  · rw [if_neg (by simpa using hg), if_neg hg]

open Classical in
/-- **Run-sum identification.** For a full coin sequence `ω`, the running sum of the gated increments over `[a, b)` on
its length-`T` prefix is the sum over the rounds `u ∈ [a, b) ∩ [0, T)` of the run on `ω` where `c` is active and every
thread fits, of (data increment − loss). -/
theorem runSum_pre (ω : ℕ → RC P) (c : ι) (a b : ℕ) : ∀ T,
    Pool.P0092.runSum (Pool.P0139.gD (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) a b) T (pre P ω T) =
      ∑ u ∈ Finset.range T, if a ≤ u ∧ u < b then
        DS P ℓ ωs φ rc0 c u (pre P ω (u + 1)) else 0
  | 0 => by simp [Pool.P0092.runSum]
  | T + 1 => by
    simp only [Pool.P0092.runSum, Finset.sum_range_succ]
    rw [init_pre, runSum_pre ω c a b T]
    congr 1
    unfold Pool.P0139.gD
    rw [init_pre]
    by_cases hab : a ≤ T ∧ T < b
    · rw [if_pos hab]
      by_cases hg : gateS P ℓ ωs φ rc0 c T (pre P ω T) = true
      · rw [if_pos ⟨hab.1, hab.2, hg⟩]
      · rw [if_neg (fun h => hg h.2.2)]
        unfold DS; rw [init_pre, if_neg hg]
    · rw [if_neg hab, if_neg (fun h => hab ⟨h.1, h.2.1⟩)]

open Classical in
/-- **The good event, on a full coin sequence.** If the length-`T` prefix of `ω` lies in P0158's `GoodV` event of
`prob_not_goodDS`, then for every interval `[a, b) ⊆ [0, T)` the sum over the rounds `u ∈ [a, b)` of the run on `ω` where
`c` is active and every thread fits, of (data increment − loss), is `< widV(Σ_{[a,b)} 1/x_{curT}, rmax1, L)` in
absolute value. These are interval tails of the actual pool data (P0186's `hlo`/`hup` shape) on active rounds. -/
theorem goodV_run (ω : ℕ → RC P) (c : ι) {L : ℝ} (T : ℕ)
    (hgood : Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T
      (pre P ω T)) (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T) :
    |∑ u ∈ Finset.Ico a b, if c ∈ active P ℓ ω ωs φ u ∧ Fits P.Lv P.sl (sp P ℓ ω ωs φ u) then
        (gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ c (u + 1) -
          gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ c u) - ℓr P ℓ u c
      else 0| <
      Pool.P0158.widV (∑ s ∈ Finset.Ico a b, rS P c s) (Pool.P0158.rmax1 (rS P c) a b) L := by
  have h := hgood a b hab hbT
  rw [runSum_pre P ℓ ωs φ rc0 ω c a b T] at h
  have hsum : (∑ u ∈ Finset.range T, if a ≤ u ∧ u < b then DS P ℓ ωs φ rc0 c u (pre P ω (u + 1)) else 0) =
      ∑ u ∈ Finset.Ico a b, DS P ℓ ωs φ rc0 c u (pre P ω (u + 1)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hsum] at h
  simpa only [DS_pre P ℓ ωs φ rc0 ω] using h

end Pool.P0203
