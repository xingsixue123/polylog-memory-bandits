import Pool.P0168.HypZ

/-!
# Walk outcomes with SAMPLED comparator copies read from the actual run

P0168's `outZ` reads a comparator copy from its own *forced* run (sampled, never a filter); for a copy the actual run
samples itself that run differs when the copy draws filter bits. As in P0086's `actEv`, `outMix` reads sampled copies
from the actual run (`outA`: retired first → `bev`, removed first → `cov`, neither → `cov T`) and the others with
P0168's per-copy `outZ`. `hypB_outMix_grid`: on the unit grid the mixed outcomes satisfy P0135's `HypB`.
-/

namespace Pool.P0186

open Finset Pool.P0156 Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0168

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ)
  (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι) (aux0 : Finset ι)
/-- First boundary in `(E c, T]` at which `c` is retired in the actual run. -/
noncomputable def aRet (T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : Option ℕ :=
  open Classical in
  if h : ∃ y, E c < y ∧ y ≤ T ∧ c ∈ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ y).aux then some (Nat.find h)
  else none
/-- First boundary in `(E c, T]` at which `c` is in no pool of the actual run. -/
noncomputable def aRem (T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : Option ℕ :=
  open Classical in
  if h : ∃ y, E c < y ∧ y ≤ T ∧ ¬ ∃ r ℓ, c ∈ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ y).pools r ℓ then
    some (Nat.find h)
  else none
/-- Outcome of a copy read from the actual run; a copy neither retired nor removed before `T` is `cov T`. -/
noncomputable def outA (jmax T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : Pool.P0135.Out :=
  match aRet E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c, aRem E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c with
  | some e, none => .bev e (min (curT E thr0 D Bt c e) jmax)
  | some e, some e' => if e ≤ e' then .bev e (min (curT E thr0 D Bt c e) jmax) else .cov e'
  | none, some e' => .cov e'
  | none, none => .cov T
/-- Mixed outcomes: sampled copies from the actual run, the others from their own forced runs (rule `U c`, initial
state `A c`). -/
noncomputable def outMix (U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι)
    (A : ι → Finset ι) (jmax T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : Pool.P0135.Out :=
  if ωs c = true then outA E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c
  else outZ E thr0 θ R K D Lv Bt lev (U c) (A c) jmax T ωs φ c

variable {E thr0 θ R K D Lv Bt lev upd aux0}

section Specs

variable {T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}
lemma aRet_spec {c : ι} {e : ℕ} (he : aRet E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e) :
    E c < e ∧ e ≤ T ∧ c ∈ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ e).aux ∧
      ∀ y, E c < y → y < e → c ∉ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ y).aux := by
  classical
  unfold aRet at he
  split_ifs at he with h
  simp only [Option.some.injEq] at he
  obtain ⟨hae, heT, hin⟩ := he ▸ Nat.find_spec h
  exact ⟨hae, heT, hin, fun y h1 h2 hy => Nat.find_min h (he ▸ h2) ⟨h1, by omega, hy⟩⟩
lemma aRem_spec (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι} (hs : ωs c = true)
    (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c) {e : ℕ}
    (he : aRem E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e) :
    E c < e ∧ e ≤ T ∧
      (∀ y, E c < y → y < e → Alive E thr0 (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) θ R K D Lv Bt lev
        ωs φ y c) ∧
      ∃ x, x + 1 = e ∧ E c ≤ x ∧
        SAlive E thr0 (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) θ R K D Lv Bt lev ωs φ x c ∧
        ¬ Alive E thr0 (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) θ R K D Lv Bt lev ωs φ e c ∧
        Bt (curT E thr0 D Bt c x) ∣ e := by
  classical
  set C := gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ with hC
  have hal : ∀ y, Alive E thr0 C θ R K D Lv Bt lev ωs φ y c ↔
      ∃ r ℓ, c ∈ (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ y).pools r ℓ := by
    intro y; rw [gRun_pools_eq]; rfl
  unfold aRem at he
  split_ifs at he with h
  simp only [Option.some.injEq] at he
  obtain ⟨hae, heT, hna⟩ := he ▸ Nat.find_spec h
  have hmin : ∀ y, E c < y → y < e → Alive E thr0 C θ R K D Lv Bt lev ωs φ y c := by
    intro y h1 h2
    rw [hal]
    by_contra hc'
    exact Nat.find_min h (he ▸ h2) ⟨h1, by omega, hc'⟩
  have hna' : ¬ Alive E thr0 C θ R K D Lv Bt lev ωs φ e c := by rw [hal]; exact hna
  have hs0 : SAlive E thr0 C θ R K D Lv Bt lev ωs φ (E c) c := salive_entry hD hLv hs hthr hent
  obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := removal_dvd hD hLv hlev hs0 e hae hna'
  have hxe : x + 1 = e := by
    by_contra hne
    exact hx4 (hmin (x + 1) (by omega) (by omega))
  subst hxe
  exact ⟨hae, heT, hmin, x, rfl, hx1, hx3, hx4, hx5⟩
lemma outA_cov {jmax : ℕ} {c : ι} {e : ℕ} (h : outA E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c = .cov e) :
    (aRem E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e ∧
      ∀ e0, aRet E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e0 → e < e0) ∨
    (e = T ∧ aRem E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = none ∧
      aRet E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = none) := by
  unfold outA at h
  split at h
  · cases h
  · rename_i e1 e2 h1 h2
    split_ifs at h with hle
    cases h
    exact Or.inl ⟨h2, fun e0 he0 => by rw [h1] at he0; cases he0; omega⟩
  · rename_i e2 h1 h2
    cases h
    exact Or.inl ⟨h2, fun e0 he0 => by rw [h1] at he0; cases he0⟩
  · rename_i h1 h2
    cases h
    exact Or.inr ⟨rfl, h2, h1⟩
lemma outA_bev {jmax : ℕ} {c : ι} {e j : ℕ}
    (h : outA E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c = .bev e j) :
    aRet E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e ∧ j = min (curT E thr0 D Bt c e) jmax ∧
      ∀ e', aRem E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = some e' → e ≤ e' := by
  unfold outA at h
  split at h
  · rename_i e1 h1 h2
    cases h
    exact ⟨h1, rfl, fun e' he' => by rw [h2] at he'; cases he'⟩
  · rename_i e1 e2 h1 h2
    split_ifs at h with hle
    cases h
    exact ⟨h1, rfl, fun e' he' => by rw [h2] at he'; cases he'; exact hle⟩
  · cases h
  · cases h
/-- A covered actual outcome of a sampled copy satisfies P0065's removal schedule (or is the horizon). -/
lemma outA_cov_sched (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (hT : Bt 0 ∣ T)
    {jmax : ℕ} {c : ι} {e : ℕ} (hs : ωs c = true) (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c) (hcT : E c < T)
    (h : outA E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c = .cov e) :
    e ≤ T ∧ Bt (thr0 c) ∣ e ∧ E c + Bt (thr0 c) ≤ e ∧
      (∀ i m, i < thr0 c → Bt i ∣ m → E c < m → m < e → Bt i ∣ e) := by
  rcases outA_cov h with ⟨hev, -⟩ | ⟨heT, -, -⟩
  · obtain ⟨-, heT, -, x, hxe, hx1, -, -, hrem⟩ := aRem_spec hB.hD hLv hlev hs hthr hent hev
    have := removal_hyp (E := E) (thr0 := thr0) (D := D) (Bt := Bt) hB (c := c) hthr hent (x := x) hx1
      (hxe ▸ hrem)
    rw [hxe] at this
    exact ⟨heT, this.1, this.2.1, this.2.2⟩
  · subst heT
    have hdT : Bt (thr0 c) ∣ e := (hB.dvd_of_le (Nat.zero_le _) hthr).trans hT
    refine ⟨le_rfl, hdT, ?_, fun i m _ hm _ _ => (hB.dvd_of_le (Nat.zero_le _) (by omega)).trans hT⟩
    obtain ⟨k, hk⟩ := hent
    obtain ⟨m, hm⟩ := hdT
    have hpos := hB.pos (thr0 c)
    have : k < m := by
      by_contra hc; push Not at hc
      have : Bt (thr0 c) * m ≤ Bt (thr0 c) * k := Nat.mul_le_mul_left _ hc
      omega
    have : Bt (thr0 c) * (k + 1) ≤ Bt (thr0 c) * m := Nat.mul_le_mul_left _ this
    rw [hk, hm]; nlinarith

end Specs

section Hyp

variable {T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}
/-- **On the unit grid the mixed outcomes satisfy P0135's `HypB`** (`R = D`, `B = Bt`, no free copies): sampled
comparator copies read from the actual run, the others from their own forced runs. -/
theorem hypB_outMix_grid (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι) (A : ι → Finset ι)
    (hE : ∀ j a, j < D → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j < D → Bt j ∣ a → a < T → thr0 (cstar j a) = j) :
    Pool.P0135.HypB D T Bt
      (fun τ r => outMix E thr0 θ R K D Lv Bt lev upd aux0 U A (D - 1) T ωs φ (cstar r τ))
      (fun _ => .bad) := by
  have hD := hB.hD
  have hZ := hypB_outZ_grid_each (θ := θ) (R := R) (lev := lev) (ωs := ωs) (φ := φ) hB hLv hlev hT cstar U A hE hthr
  have hcv : ∀ τ r e, Bt r ∣ τ → τ < T → r < D →
      outMix E thr0 θ R K D Lv Bt lev upd aux0 U A (D - 1) T ωs φ (cstar r τ) = .cov e →
      τ + Bt r ≤ e ∧ e ≤ T ∧ Bt r ∣ e ∧ ∀ j m, j < r → Bt j ∣ m → τ < m → m < e → Bt j ∣ e := by
    intro τ r e hd hτ hr h; unfold outMix at h; split_ifs at h with hs
    · have hE' := hE r τ hr hd hτ
      have hthr' := hthr r τ hr hd hτ
      have := outA_cov_sched hB hLv hlev hT hs (by rw [hthr']; exact hr) (by rw [hthr', hE']; exact hd)
        (by rw [hE']; exact hτ) h
      rw [hthr', hE'] at this
      exact ⟨this.2.2.1, this.1, this.2.1, this.2.2.2⟩
    · exact ⟨hZ.lb τ r e hd hτ hr h, hZ.ub τ r e hd hτ hr h, hZ.edvd τ r e hd hτ hr h, hZ.align τ r e hd hτ hr h⟩
  have hbb : ∀ τ r e j, Bt r ∣ τ → τ < T → r < D →
      outMix E thr0 θ R K D Lv Bt lev upd aux0 U A (D - 1) T ωs φ (cstar r τ) = .bev e j →
      (τ < e ∧ e ≤ T ∧ j ≤ r) ∧ ∀ i m, i < j → Bt i ∣ m → τ < m → m ≤ e → False := by
    intro τ r e j hd hτ hr h; unfold outMix at h; split_ifs at h with hs
    · obtain ⟨hev, rfl, -⟩ := outA_bev h
      have hE' := hE r τ hr hd hτ
      obtain ⟨hae, heT, -⟩ := aRet_spec hev
      have := curT_le_thr0 (E := E) (thr0 := thr0) (D := D) (Bt := Bt) (cstar r τ) e
      rw [hthr r τ hr hd hτ] at this
      exact ⟨⟨hE' ▸ hae, heT, by omega⟩, fun i m hi hm h1 h2 =>
        nob_of_le_curT (cstar r τ) (min_le_left _ _) hi hm (by rw [hE']; exact h1) h2⟩
    · exact ⟨hZ.blt τ r e j hd hτ hr h, hZ.bnc τ r e j hd hτ hr h⟩
  exact
    { pos := hB.pos, dvd := fun r hr => hB.dvd r hr, hR := hD, hT := hT
      lb := fun τ r e hd hτ hr h => (hcv τ r e hd hτ hr h).1
      ub := fun τ r e hd hτ hr h => (hcv τ r e hd hτ hr h).2.1
      edvd := fun τ r e hd hτ hr h => (hcv τ r e hd hτ hr h).2.2.1
      align := fun τ r e hd hτ hr h => (hcv τ r e hd hτ hr h).2.2.2
      blt := fun τ r e j hd hτ hr h => (hbb τ r e j hd hτ hr h).1
      bnc := fun τ r e j hd hτ hr h => (hbb τ r e j hd hτ hr h).2
      flt := fun _ _ _ h => (by cases h), falign := fun _ _ _ h => (by cases h)
      fblt := fun _ _ _ _ h => (by cases h), fbnc := fun _ _ _ _ h => (by cases h) }

end Hyp

end Pool.P0186
