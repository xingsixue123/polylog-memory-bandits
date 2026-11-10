import Pool.P0194.Proc

/-!
# Locality in the sampling and filter coins, and coin-sum tools for coin algorithms

* `startPools_congr_ωs`, `gRun_congr_ωs`: P0065's sampling at unit `a` reads only the sampling bits of copies entering
  at `a`; P0156's generic process `gRun` at boundary `a` reads only those of copies entering before `a` (P0156's
  `gRun_congr_φ` is the filter-bit analogue).
* For P0194's per-thread round-level process: `AgreeS` / `AgreeS'` (agreement of sampling bits on copies entering before
  `u` / up to `u`, and of filter bits on units before `u`), `pool_congr_s`, `sp_congr_s`, `active_congr_s`, `sA_congr_s`,
  `occAtS_congr_s`, `algCh_congr_s` and **`play_congr_s`**: the play at round `u` reads only the sampling bits of copies
  entering at rounds `≤ u` and the filter bits of units `< u` (P0194's own `*_congr` lemmas are about the round coins).
* For P0050 coin algorithms: **`sum_W_restrict`** (future coins integrate out), `run_congr` (the run reads only earlier
  coins), `ext` (a finite coin sequence extended by a default coin) and **`sum_expLoss_eq`** (the total expected loss
  over `T` rounds is one coin sum over `T` rounds of coins).
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0065 Pool.P0052 Pool.P0194

namespace Pool.P0205

section GRun

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) {σ : Type*}

/-- Sampling at unit `a` reads only the sampling bits of copies entering at `a`. -/
theorem startPools_congr_ωs {ωs ωs' : ι → Bool} (a : ℕ) (P : ℕ → ℕ → Finset ι)
    (h : ∀ c, E c = a → ωs c = ωs' c) :
    startPools E thr0 D Lv Bt ωs a P = startPools E thr0 D Lv Bt ωs' a P := by
  have : newAtT E thr0 ωs a = newAtT E thr0 ωs' a := by
    funext r
    unfold newAtT
    refine Finset.filter_congr fun c _ => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [← h c h1]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h c h1]; exact h3⟩
  unfold startPools sample
  rw [this]

/-- P0156's `gRun` at boundary `a` reads only the sampling bits of copies entering before `a`. -/
theorem gRun_congr_ωs (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → σ → (ι → ℝ) × σ) (aux0 : σ)
    {ωs ωs' : ι → Bool} (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a, (∀ c, E c < a → ωs c = ωs' c) →
      Pool.P0156.gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a =
        Pool.P0156.gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs' φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have ih' := ih (fun c hc => h c (by omega))
    simp only [Pool.P0156.gRun]
    rw [ih', startPools_congr_ωs E thr0 D Lv Bt a _ (fun c hc => h c (by omega))]

end GRun

section Proc

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] {P : ParD n ι} (ℓ : LossSeq n) (ω : ℕ → RC P)

/-- Agreement of sampling bits on copies entering before `u` and of filter bits on units before `u`. -/
def AgreeS (ωs ωs' : ι → Bool) (φ φ' : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (u : ℕ) : Prop :=
  (∀ c, P.E c < u → ωs c = ωs' c) ∧ ∀ r, ∀ a < u, φ r a = φ' r a

variable {ωs ωs' : ι → Bool} {φ φ' : ℕ → ℕ → ℕ → Fin P.K → ι → Bool}

theorem AgreeS.mono {u v : ℕ} (h : AgreeS ωs ωs' φ φ' u) (hv : v ≤ u) : AgreeS ωs ωs' φ φ' v :=
  ⟨fun c hc => h.1 c (by omega), fun r a ha => h.2 r a (by omega)⟩

theorem pool_congr_s {u : ℕ} (h : AgreeS ωs ωs' φ φ' u) : pool P ℓ ω ωs φ u = pool P ℓ ω ωs' φ' u := by
  unfold pool Pool.P0176.dzRun
  rw [gRun_congr_ωs _ _ _ _ _ _ _ _ _ _ _ _ u h.1]
  exact Pool.P0156.gRun_congr_φ _ _ _ _ _ _ _ _ _ _ _ _ u (fun r a ha => h.2 r a ha)

theorem sp_congr_s {u : ℕ} (h : AgreeS ωs ωs' φ φ' u) (hu : ∀ c, P.E c = u → ωs c = ωs' c) :
    sp P ℓ ω ωs φ u = sp P ℓ ω ωs' φ' u := by
  unfold sp
  rw [pool_congr_s ℓ ω h]
  exact startPools_congr_ωs _ _ _ _ _ u _ hu

/-- Agreement up to and including the entries of round `u`. -/
def AgreeS' (ωs ωs' : ι → Bool) (φ φ' : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (u : ℕ) : Prop :=
  AgreeS ωs ωs' φ φ' u ∧ ∀ c, P.E c = u → ωs c = ωs' c

theorem AgreeS'.mono {u v : ℕ} (h : AgreeS' ωs ωs' φ φ' u) (hv : v ≤ u) : AgreeS' ωs ωs' φ φ' v := by
  rcases Nat.lt_or_eq_of_le hv with hv | rfl
  · exact ⟨h.1.mono (by omega), fun c hc => h.1.1 c (by omega)⟩
  · exact h

theorem active_congr_s {u : ℕ} (h : AgreeS' ωs ωs' φ φ' u) :
    active P ℓ ω ωs φ u = active P ℓ ω ωs' φ' u := by
  unfold active; rw [sp_congr_s ℓ ω h.1 h.2, pool_congr_s ℓ ω h.1]

theorem sA_congr_s : ∀ u, AgreeS' ωs ωs' φ φ' u → sA P ℓ ω ωs φ u = sA P ℓ ω ωs' φ' u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro h
    have h' : AgreeS' ωs ωs' φ φ' u := h.mono (by omega)
    simp only [sA]
    rw [ih h', active_congr_s ℓ ω h']

theorem occAtS_congr_s {u : ℕ} (h : AgreeS' ωs ωs' φ φ' u) (s : Σ j : Fin P.D, Fin (P.sl j)) :
    occAtS P ℓ ω ωs φ u s = occAtS P ℓ ω ωs' φ' u s := by
  unfold occAtS; rw [sp_congr_s ℓ ω h.1 h.2, pool_congr_s ℓ ω h.1]

theorem algCh_congr_s {u : ℕ} (h : AgreeS' ωs ωs' φ φ' u) :
    algCh P ℓ ω ωs φ u = algCh P ℓ ω ωs' φ' u := by
  unfold algCh; rw [sA_congr_s ℓ ω u h, active_congr_s ℓ ω h]

/-- **The play at round `u` reads only the sampling bits of copies entering at rounds `≤ u` and the filter bits of
units `< u`.** -/
theorem play_congr_s {u : ℕ} (h : AgreeS' ωs ωs' φ φ' u) :
    play P ℓ ω ωs φ u = play P ℓ ω ωs' φ' u := by
  unfold play
  rw [algCh_congr_s ℓ ω h, funext (occAtS_congr_s ℓ ω h)]

end Proc

section Generic

variable {n : ℕ} (A : CoinAlg n)

attribute [local instance] CoinAlg.fS CoinAlg.fY CoinAlg.fZ

/-- Future coins integrate out. -/
theorem sum_W_restrict (k : ℕ) (F : (Fin k → A.Y × A.Z) → ℝ) :
    ∀ T (h : k ≤ T), ∑ ω : Fin T → A.Y × A.Z, A.W ω * F (fun i => ω (Fin.castLE h i)) =
      ∑ ω : Fin k → A.Y × A.Z, A.W ω * F ω := by
  intro T h
  induction T, h using Nat.le_induction with
  | base => rfl
  | succ T hkT ih =>
    rw [sum_split]
    have e : ∀ (ω' : Fin T → A.Y × A.Z) (x : A.Y × A.Z),
        (fun i : Fin k => (Fin.snoc ω' x : Fin (T + 1) → A.Y × A.Z) (Fin.castLE (Nat.le_succ_of_le hkT) i)) =
          fun i => ω' (Fin.castLE hkT i) := by
      intro ω' x; funext i
      have : (Fin.castLE (Nat.le_succ_of_le hkT) i : Fin (T + 1)) = Fin.castSucc (Fin.castLE hkT i) := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    simp only [W_snoc, e]
    rw [Finset.sum_comm]
    have h1 : ∑ x : A.Y × A.Z, (A.μ x.1).toReal * (A.ν x.2).toReal = 1 := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, pmf_sum_toReal, mul_one]
    have h2 : ∀ ω' : Fin T → A.Y × A.Z, ∑ x : A.Y × A.Z, A.W ω' * ((A.μ x.1).toReal * (A.ν x.2).toReal) *
        F (fun i => ω' (Fin.castLE hkT i)) = A.W ω' * F (fun i => ω' (Fin.castLE hkT i)) := by
      intro ω'; rw [← Finset.sum_mul, ← Finset.mul_sum, h1, mul_one]
    simp only [h2]
    exact ih

/-- The run reads only the coins of earlier rounds. -/
theorem run_congr (ℓ : LossSeq n) {ω ω' : ℕ → A.Y × A.Z} : ∀ t, (∀ j < t, ω j = ω' j) →
    A.run ℓ ω t = A.run ℓ ω' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    simp only [CoinAlg.run]
    rw [ih (fun j hj => h j (by omega)), h t (by omega)]

/-- A finite coin sequence extended by a default coin. -/
def ext {T : ℕ} (ω₀ : A.Y × A.Z) (ω : Fin T → A.Y × A.Z) : ℕ → A.Y × A.Z :=
  fun j => if h : j < T then ω ⟨j, h⟩ else ω₀

/-- **Total expected loss over `T` rounds** as one coin sum over `T` rounds of coins. -/
theorem sum_expLoss_eq (ℓ : LossSeq n) (ω₀ : A.Y × A.Z) (T : ℕ) :
    ∑ t ∈ range T, A.toMachine.expLoss ℓ t =
      ∑ ω : Fin T → A.Y × A.Z, A.W ω * ∑ t ∈ range T,
        ((ℓ t (A.act t (A.run ℓ (ext A ω₀ ω) t) (ext A ω₀ ω t).1)).toNat : ℝ) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t + 1 ≤ T := Finset.mem_range.mp ht
  rw [expLoss_eq_coins_run A ℓ t (fun _ => ω₀)]
  rw [← sum_W_restrict A (t + 1) _ T ht']
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  have hrun : A.run ℓ (fun j => if h : j < t + 1 then ω (Fin.castLE ht' ⟨j, h⟩) else ω₀) t =
      A.run ℓ (ext A ω₀ ω) t :=
    run_congr A ℓ t fun j hj => by
      simp only [ext, dif_pos (show j < t + 1 by omega), dif_pos (show j < T by omega)]; rfl
  have hlast : (ω (Fin.castLE ht' (Fin.last t))).1 = (ext A ω₀ ω t).1 := by
    simp only [ext, dif_pos (show t < T by omega)]; rfl
  rw [hrun, hlast]

end Generic

end Pool.P0205
