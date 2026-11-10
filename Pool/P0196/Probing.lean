import Pool.P0187.Identity

open Finset Pool.P0001 Pool.P0050 Pool.P0181

namespace Pool.P0196

/-- **Checks every `Bmin` rounds.** If a partial sum of increments `g ≤ 1` started at `a` is `≤ M` at every check
boundary `m` (`Bmin ∣ m`, `a < m < b`), then the whole sum over `[a, b)` is `≤ M + Bmin`. -/
theorem sum_le_of_checks (g : ℕ → ℝ) (hg : ∀ t, g t ≤ 1) (a b Bmin : ℕ) (hab : a ≤ b) (hB : 0 < Bmin)
    (M : ℝ) (hM : 0 ≤ M)
    (hcheck : ∀ m, a < m → m < b → Bmin ∣ m → ∑ t ∈ Ico a m, g t ≤ M) :
    ∑ t ∈ Ico a b, g t ≤ M + Bmin := by
  have hlen : ∀ c d, c ≤ d → ∑ t ∈ Ico c d, g t ≤ ((d - c : ℕ) : ℝ) := by
    intro c d _
    calc ∑ t ∈ Ico c d, g t ≤ ∑ _t ∈ Ico c d, (1 : ℝ) := Finset.sum_le_sum fun t _ => hg t
      _ = ((d - c : ℕ) : ℝ) := by simp
  by_cases hsmall : b - a ≤ Bmin
  · have := hlen a b hab
    have : ((b - a : ℕ) : ℝ) ≤ Bmin := by exact_mod_cast hsmall
    linarith
  · push_neg at hsmall
    set m := Bmin * ((b - 1) / Bmin) with hm
    have hm1 : m ≤ b - 1 := Nat.mul_div_le (b - 1) Bmin
    have hm2 : b - 1 < m + Bmin := by
      have := Nat.lt_mul_div_succ (b - 1) hB
      rw [hm]; nlinarith [Nat.div_add_mod (b - 1) Bmin, Nat.mod_lt (b - 1) hB]
    have ham : a < m := by omega
    have hmb : m < b := by omega
    have hdvd : Bmin ∣ m := Dvd.intro _ rfl
    have h1 := hcheck m ham hmb hdvd
    have h2 := hlen m b hmb.le
    have h3 : ((b - m : ℕ) : ℝ) ≤ Bmin := by exact_mod_cast (by omega : b - m ≤ Bmin)
    rw [← Finset.sum_Ico_consecutive _ ham.le hmb.le]
    linarith

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : Par n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

lemma match_eq_sum (o : Option ι) (f : ι → ℝ) :
    (match o with | some x => f x | none => 0) = ∑ x, if o = some x then f x else 0 := by
  rcases o with _ | x
  · simp
  · simp [Finset.sum_ite_eq', eq_comm]

/-- Number of slot positions holding member `x` at round `t`. -/
noncomputable def nSlots (ω : ℕ → RC P) (t : ℕ) (x : ι) : ℕ :=
  (univ.filter fun y : Fin P.S => P.isSlot y = true ∧ occAt P ℓ ωs φ ω t y = some x).card

/-- The probing value of a round, member by member. -/
theorem sum_probeVal_eq (ω : ℕ → RC P) (t : ℕ) :
    ∑ y : Fin P.S, Pool.P0187.probeVal P ℓ ωs φ ω t y
      = ∑ x : ι, (nSlots P ℓ ωs φ ω t x : ℝ) * (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) := by
  have : ∀ y : Fin P.S, Pool.P0187.probeVal P ℓ ωs φ ω t y = ∑ x : ι,
      if (P.isSlot y = true ∧ occAt P ℓ ωs φ ω t y = some x) then
        (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) else 0 := by
    intro y
    unfold Pool.P0187.probeVal
    by_cases h : P.isSlot y = true
    · simp only [h, if_true, true_and]
      exact match_eq_sum _ _
    · simp only [Bool.not_eq_true] at h
      simp [h]
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- **Probing total.** If every active member holds exactly one slot position and no other copy holds one
(`hplace`, a no-overflow layout property), and each member's sum of per-round gaps against BASE over its
active rounds is at most `Γ x`, then the probing sum over `T` rounds is at most `Σ_{x ever active} Γ x`. -/
theorem probe_total_le (ω : ℕ → RC P) (T : ℕ) (Γ : ι → ℝ)
    (hplace : ∀ t < T, ∀ x, nSlots P ℓ ωs φ ω t x = if x ∈ active P ℓ ω ωs φ t then 1 else 0)
    (hΓ : ∀ x, ∑ t ∈ (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t),
        (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) ≤ Γ x) :
    ∑ t ∈ range T, ∑ y : Fin P.S, Pool.P0187.probeVal P ℓ ωs φ ω t y
      ≤ ∑ x ∈ univ.filter (fun x => ∃ t < T, x ∈ active P ℓ ω ωs φ t), Γ x := by
  have h1 : ∑ t ∈ range T, ∑ y : Fin P.S, Pool.P0187.probeVal P ℓ ωs φ ω t y
      = ∑ x : ι, ∑ t ∈ (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t),
          (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) := by
    rw [Finset.sum_congr rfl fun t ht => sum_probeVal_eq P ℓ ωs φ ω t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [hplace t (Finset.mem_range.mp ht) x]
    split_ifs <;> simp
  rw [h1, ← Finset.sum_filter_add_sum_filter_not univ (fun x => ∃ t < T, x ∈ active P ℓ ω ωs φ t)]
  have h0 : ∑ x ∈ univ.filter (fun x => ¬ ∃ t < T, x ∈ active P ℓ ω ωs φ t),
      ∑ t ∈ (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t),
        (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    have : (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t ht hta
      exact hx.2 ⟨t, Finset.mem_range.mp ht, hta⟩
    rw [this, Finset.sum_empty]
  rw [h0, add_zero]
  exact Finset.sum_le_sum fun x _ => hΓ x

/-- The estimated gap of copy `x` against BASE at boundary `m`, as read by rule (b″). -/
noncomputable def estGap (ω : ℕ → RC P) (x : ι) (m : ℕ) : ℝ :=
  (pool P ℓ ω ωs φ m).est x m - (pool P ℓ ω ωs φ m).est x (P.E x) - (Bh P ℓ ω m - Bh P ℓ ω (P.E x))

/-- **The rule did not fire.** If `x` is active at rounds `c` and `c + 1`, `E x ≤ c` and `Bmin ∣ c + 1`, then
its estimated gap at `c + 1` is below the margin `Λ x c`. -/
theorem estGap_lt (ω : ℕ → RC P) (x : ι) (c : ℕ) (hc : x ∈ active P ℓ ω ωs φ c)
    (hc1 : x ∈ active P ℓ ω ωs φ (c + 1)) (hE : P.E x ≤ c) (hB : P.Bmin ∣ c + 1) :
    estGap P ℓ ωs φ ω x (c + 1) < P.Λ x c := by
  unfold active at hc hc1
  rw [Finset.mem_sdiff] at hc hc1
  have hnot := hc1.2
  unfold pool at hnot
  rw [Pool.P0156.mem_aux_succ] at hnot
  push_neg at hnot
  have hrule := hnot.2 hc.1
  by_contra hge
  push_neg at hge
  apply hrule
  unfold rhZ
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hE, hB⟩, ?_⟩
  unfold estGap pool at hge
  exact hge

/-- **Per-member bound.** Let `x` be active exactly on `[E x, b)` within the horizon, let the true gap since entry
be at most the estimated gap plus `W` at every check boundary inside, and let the margins be `≤ Λb`. Then the
member's total gap against BASE over its active rounds is `≤ Λb + W + Bmin`. -/
theorem member_le (ω : ℕ → RC P) (T : ℕ) (x : ι) (b : ℕ) (hbT : b ≤ T) (hEb : P.E x ≤ b)
    (hB : 0 < P.Bmin) (Λb W : ℝ) (hM : 0 ≤ Λb + W)
    (hΛ : ∀ c, P.E x ≤ c → c + 1 < b → P.Λ x c ≤ Λb)
    (hint : ∀ t < T, x ∈ active P ℓ ω ωs φ t ↔ P.E x ≤ t ∧ t < b)
    (hconc : ∀ m, P.E x < m → m < b → P.Bmin ∣ m →
      ∑ t ∈ Ico (P.E x) m, (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) ≤ estGap P ℓ ωs φ ω x m + W) :
    ∑ t ∈ (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t),
      (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) ≤ Λb + W + P.Bmin := by
  have hset : (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t) = Ico (P.E x) b := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨ht, ha⟩; exact (hint t ht).1 ha
    · rintro ⟨h1, h2⟩; exact ⟨by omega, (hint t (by omega)).2 ⟨h1, h2⟩⟩
  rw [hset]
  have hg : ∀ t, ((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t ≤ 1 := by
    intro t
    have h1 : ((ℓ t (P.arm x)).toNat : ℝ) ≤ 1 := by
      cases ℓ t (P.arm x) <;> simp
    have h2 : 0 ≤ bPol P ℓ ω t := by
      unfold bPol
      exact Finset.sum_nonneg fun yB _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
    linarith
  apply sum_le_of_checks _ hg (P.E x) b P.Bmin hEb hB (Λb + W) hM
  intro m hm1 hm2 hdvd
  have hc := hconc m hm1 hm2 hdvd
  have hm0 : 1 ≤ m := by omega
  have hlt := estGap_lt P ℓ ωs φ ω x (m - 1)
    ((hint (m - 1) (by omega)).2 ⟨by omega, by omega⟩)
    (by rw [show m - 1 + 1 = m by omega]; exact (hint m (by omega)).2 ⟨by omega, hm2⟩)
    (by omega) (by rw [show m - 1 + 1 = m by omega]; exact hdvd)
  rw [show m - 1 + 1 = m by omega] at hlt
  linarith [hΛ (m - 1) (by omega) (by omega)]

/-- **Probing term, pathwise (C9).** Under the one-slot placement (`hplace`), and for every ever-active member an
active interval `[E x, b x)` and the concentration bound at its checks, the probing sum over `T` rounds is at most
`(Λb + W + Bmin)·#(ever-active members)`. -/
theorem probe_total_le_count (ω : ℕ → RC P) (T : ℕ) (b : ι → ℕ) (hB : 0 < P.Bmin) (Λb W : ℝ)
    (hM : 0 ≤ Λb + W)
    (hplace : ∀ t < T, ∀ x, nSlots P ℓ ωs φ ω t x = if x ∈ active P ℓ ω ωs φ t then 1 else 0)
    (hbT : ∀ x, (∃ t < T, x ∈ active P ℓ ω ωs φ t) → b x ≤ T)
    (hEb : ∀ x, (∃ t < T, x ∈ active P ℓ ω ωs φ t) → P.E x ≤ b x)
    (hint : ∀ x, (∃ t < T, x ∈ active P ℓ ω ωs φ t) →
      ∀ t < T, x ∈ active P ℓ ω ωs φ t ↔ P.E x ≤ t ∧ t < b x)
    (hΛ : ∀ x, (∃ t < T, x ∈ active P ℓ ω ωs φ t) → ∀ c, P.E x ≤ c → c + 1 < b x → P.Λ x c ≤ Λb)
    (hconc : ∀ x, (∃ t < T, x ∈ active P ℓ ω ωs φ t) → ∀ m, P.E x < m → m < b x → P.Bmin ∣ m →
      ∑ t ∈ Ico (P.E x) m, (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) ≤ estGap P ℓ ωs φ ω x m + W) :
    ∑ t ∈ range T, ∑ y : Fin P.S, Pool.P0187.probeVal P ℓ ωs φ ω t y
      ≤ (Λb + W + P.Bmin) * ((univ.filter (fun x => ∃ t < T, x ∈ active P ℓ ω ωs φ t)).card : ℝ) := by
  have hB' : (0 : ℝ) ≤ P.Bmin := Nat.cast_nonneg _
  have hΓ : ∀ x, ∑ t ∈ (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t),
      (((ℓ t (P.arm x)).toNat : ℝ) - bPol P ℓ ω t) ≤ Λb + W + P.Bmin := by
    intro x
    by_cases hx : ∃ t < T, x ∈ active P ℓ ω ωs φ t
    · exact member_le P ℓ ωs φ ω T x (b x) (hbT x hx) (hEb x hx) hB Λb W hM (hΛ x hx) (hint x hx)
        (hconc x hx)
    · have : (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro t ht hta
        exact hx ⟨t, Finset.mem_range.mp ht, hta⟩
      rw [this, Finset.sum_empty]
      linarith
  have h := probe_total_le P ℓ ωs φ ω T (fun _ => Λb + W + P.Bmin) hplace hΓ
  rw [Finset.sum_const, nsmul_eq_mul] at h
  linarith

end Pool.P0196
