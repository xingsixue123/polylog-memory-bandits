import Pool.P0109.GoodFO

/-!
# A generic adapted-data threaded pool process, and its pool sizes (generalizing P0095/P0109)

P0095's one-free-observation process updates each copy's cover data by `s·L` when the copy is observed in its slot.
P0109 shows that P0073's pool-size bound survives this adapted data. Its proof uses only three facts:
1. the pools are P0065's `tpools` on the realized data;
2. the data up to time `a + 1` read only filter bits of units `< a`;
3. the increments are bounded.

This file isolates them. In `gRun`, each unit `a` does three things:
* it forms the start pools (P0065's inheritance and sampling);
* an **arbitrary update rule** `upd a sp est aux` returns every copy's data increment for the unit and a new auxiliary
  state `aux`. The rule may read the start pools `sp`, the data history `est`, and its own auxiliary state, e.g. a set
  of retired copies;
* threads whose epoch ends merge with the updated data, as in P0095.

* `gRun_pools_eq`: the pools are `tpools` on the realized data `gChat`.
* `gRun_congr_φ`, `gChat_congr_φ`: locality in the filter bits.
* `Lint_gChat_bounds`: increments in `[0, m]` give data increments in `[0, m·len]`.
* `prob_members_large_gen`: P0109's `prob_members_large_FO` for every such process, for every fixed update rule
  (fixed slot sequence, fixed BASE data, ...).

`fo_upd` / `foRun_eq_gRun` recover P0095's process as an instance.
-/

namespace Pool.P0156

open Finset Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0046 Pool.P0073 Pool.P0109

section Proc

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) {σ : Type*}

/-- State at a boundary: pools, data history, auxiliary state. -/
structure GSt (ι σ : Type*) where
  pools : ℕ → ℕ → Finset ι
  est : ι → ℕ → ℝ
  aux : σ

/-- Data update after unit `a` with per-copy increments `inc`: the history up to `a` is kept. -/
def gStep (a : ℕ) (inc : ι → ℝ) (est : ι → ℕ → ℝ) : ι → ℕ → ℝ :=
  fun x t => if t ≤ a then est x t else est x a + inc x

/-- **The generic adapted-data threaded process.** `upd a sp est aux = (increments, new aux)`. -/
noncomputable def gRun (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → σ → (ι → ℝ) × σ) (aux0 : σ)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ℕ → GSt ι σ
  | 0 => ⟨fun _ _ => ∅, fun _ _ => 0, aux0⟩
  | a + 1 =>
    let st := gRun upd aux0 ωs φ a
    let sp := startPools E thr0 D Lv Bt ωs a st.pools
    let u := upd a sp st.est st.aux
    ⟨fun r => if Bt r ∣ a + 1 then
        mergeUpTo E (gStep a u.1 st.est) θ R K (φ r) a (lev r a) (sp r) else sp r,
     gStep a u.1 st.est, u.2⟩

variable (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → σ → (ι → ℝ) × σ) (aux0 : σ)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- The increments of unit `a`. -/
noncomputable def gInc (a : ℕ) : ι → ℝ :=
  (upd a (startPools E thr0 D Lv Bt ωs a (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).pools)
    (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).est (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).aux).1

/-- The realized data history. -/
noncomputable def gChat (x : ι) (t : ℕ) : ℝ := (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ t).est x t

theorem gRun_succ_est (a : ℕ) :
    (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ (a + 1)).est =
      gStep a (gInc E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a) (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).est :=
  rfl

theorem gRun_succ_pools (a r : ℕ) :
    (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ (a + 1)).pools r =
      if Bt r ∣ a + 1 then
        mergeUpTo E (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ (a + 1)).est θ R K (φ r) a (lev r a)
          (startPools E thr0 D Lv Bt ωs a (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).pools r)
      else startPools E thr0 D Lv Bt ωs a (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).pools r := rfl

/-- Past data are never changed. -/
theorem gEst_frozen (x : ι) {t : ℕ} : ∀ a, t ≤ a →
    (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).est x t = gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x t := by
  intro a
  induction a with
  | zero => intro h; rw [Nat.le_zero.mp h]; rfl
  | succ a ih =>
    intro h
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [gRun_succ_est]
      simp only [gStep, show t ≤ a by omega, if_true]
      exact ih (by omega)
    · subst h; rfl

/-- The data increment of unit `a`. -/
theorem gChat_succ (x : ι) (a : ℕ) :
    gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x (a + 1) =
      gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x a + gInc E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a x := by
  show (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ (a + 1)).est x (a + 1) = _
  rw [gRun_succ_est]
  simp only [gStep, show ¬ (a + 1 ≤ a) by omega, if_false]
  rw [gEst_frozen E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x a le_rfl]

/-- **Identification.** The pools of the generic process are P0065's threaded pools on its realized data. -/
theorem gRun_pools_eq : ∀ a,
    (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a).pools =
      tpools E thr0 (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) θ R K D Lv Bt lev ωs φ a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    funext r
    show (if Bt r ∣ a + 1 then _ else _) = _
    simp only [tpools]
    rw [← ih]
    split_ifs with hB
    · refine Pool.P0083.mergeUpTo_congr E θ R K _ _ (φ r) a _ (fun j x _ u hu => ?_) (lev r a)
      exact gEst_frozen E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x (a + 1) hu
    · rfl

/-- **Locality in the filter bits.** The state at boundary `a` reads only the filter bits of units `< a`. -/
theorem gRun_congr_φ {φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool} : ∀ a, (∀ r, ∀ a' < a, φ r a' = φ' r a') →
    gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a = gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ' a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have ih' := ih (fun r a' ha' => h r a' (by omega))
    simp only [gRun]
    rw [ih']
    congr 1
    funext r
    split_ifs
    · exact Pool.P0063.mergeUpTo_congr E _ θ R K (φ r) (φ' r) a (lev r a)
        (fun ℓ _ => by rw [h r a (by omega)]) _
    · rfl

/-- The realized data up to time `a + 1` read only the filter bits of units `< a`. -/
theorem gChat_congr_φ {φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool} (a : ℕ) (h : ∀ r, ∀ a' < a, φ r a' = φ' r a')
    (x : ι) (t : ℕ) (ht : t ≤ a + 1) :
    gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x t = gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ' x t := by
  rcases Nat.lt_or_eq_of_le ht with ht | ht
  · unfold gChat
    rw [gRun_congr_φ E thr0 θ R K D Lv Bt lev upd aux0 ωs t (fun r a' ha' => h r a' (by omega))]
  · subst ht
    have hf := gRun_congr_φ E thr0 θ R K D Lv Bt lev upd aux0 ωs a h
    rw [gChat_succ, gChat_succ]
    have h1 : gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x a = gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ' x a := by
      unfold gChat; rw [hf]
    unfold gInc; rw [hf, h1]

/-- Increments in `[0, m]` give data increments in `[0, m·len]`. -/
theorem Lint_gChat_bounds {m : ℝ} (hinc : ∀ a x, 0 ≤ gInc E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a x ∧
      gInc E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a x ≤ m) (i : ι) (a : ℕ) :
    ∀ b, a ≤ b → 0 ≤ Lint (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) i a b ∧
      Lint (gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ) i a b ≤ m * ((b - a : ℕ) : ℝ) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp [Lint]
  | succ b hab ih =>
    have hstep := gChat_succ E thr0 θ R K D Lv Bt lev upd aux0 ωs φ i b
    have hi := hinc b i
    unfold Lint at ih ⊢
    rw [hstep]
    have hcast : ((b + 1 - a : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) + 1 := by
      rw [show b + 1 - a = (b - a) + 1 by omega]; push_cast; ring
    rw [hcast]
    constructor <;> nlinarith [ih.1, ih.2, hi.1, hi.2]

end Proc

section Prob

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) {σ : Type} (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → σ → (ι → ℝ) × σ) (aux0 : σ)
  {NE Lt : ℕ} (M0 : ℝ) (kk : ℕ)

/-- The data of the generic process on P0073's coin array `ω`. -/
noncomputable def gCof (ω : SlotT NE D Lt K → ι → Bool) : ι → ℕ → ℝ :=
  gChat E thr0 θ R K D Lv Bt lev upd aux0 (ωsOfT E K D ω) (φOfT K D ω)

/-- The data read by a merge iteration do not read its own filter bits. -/
theorem gCof_local (s0 : Fin NE × Fin D × Fin (Lt + 1) × Fin K) (ω ω' : SlotT NE D Lt K → ι → Bool)
    (h : ∀ s, s ≠ Sum.inr s0 → ω s = ω' s) :
    ∀ x u, u ≤ (s0.1 : ℕ) + 1 → gCof E thr0 θ R K D Lv Bt lev upd aux0 ω x u =
      gCof E thr0 θ R K D Lv Bt lev upd aux0 ω' x u := by
  intro x u hu
  unfold gCof
  rw [ωsOfT_agree (E := E) ω ω' s0 h]
  refine gChat_congr_φ E thr0 θ R K D Lv Bt lev upd aux0 _ (s0.1 : ℕ) (fun r a' ha' => ?_) x u hu
  funext ℓ k
  exact φOfT_agree ω ω' s0 h r a' ℓ k (by rintro ⟨h1, -⟩; omega)

open Classical in
/-- One merge iteration of the generic process is bad with probability `≤ delta` (P0109's `iter_slot_le_FO`). -/
theorem iter_slot_le_gen {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E)
    (Tmax : ℝ) (hC : ∀ (ω : SlotT NE D Lt K → ι → Bool) i a b, a ≤ b → b ≤ NE →
      0 ≤ Lint (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) i a b ∧
        Lint (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) i a b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (s0 : Fin NE × Fin D × Fin (Lt + 1) × Fin K) :
    ∑ ω, bw2 (qOfT K D ps p) ω *
        (if Pool.P0063.Abad E (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R M0 s0.1
            (iterInT E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev ω
              s0.1 s0.2.1 s0.2.2.1 s0.2.2.2)
            ((iterInT E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev ω
              s0.1 s0.2.1 s0.2.2.1 s0.2.2.2).filter (fun c => ω (Sum.inr s0) c = true))
          then 1 else 0) ≤ delta (Fintype.card ι) p R kk M0 := by
  have hq01 : ∀ (s : SlotT NE D Lt K) (c : ι), 0 ≤ qOfT K D ps p s c ∧ qOfT K D ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOfT, hps, hp0, hp1]
  have hw : ∀ ω : SlotT NE D Lt K → ι → Bool, 0 ≤ bw2 (qOfT K D ps p) ω := fun ω =>
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
      split_ifs
      · exact (hq01 s c).1
      · linarith [(hq01 s c).2]
  set X : (SlotT NE D Lt K → ι → Bool) → Finset ι := fun ω =>
    iterInT E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev ω s0.1 s0.2.1 s0.2.2.1 s0.2.2.2
    with hXdef
  have hX : ∀ ω ω', (∀ s, s ≠ Sum.inr s0 → ω s = ω' s) → X ω = X ω' := by
    intro ω ω' h
    simp only [hXdef]
    rw [iterInT_congrC θ R K D Lv Bt lev E thr0 _ _ ω _ _ _ _
      (fun x u hu => gCof_local E thr0 θ R K D Lv Bt lev upd aux0 s0 ω ω' h x u hu)]
    exact iterInT_local s0 ω ω' h
  set G : (SlotT NE D Lt K → ι → Bool) → Finset ι → ℝ := fun ω F =>
    if Pool.P0063.Abad E (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R M0 s0.1 (X ω) F then 1 else 0 with hGdef
  have hG : ∀ ω ω', (∀ s, s ≠ Sum.inr s0 → ω s = ω' s) → G ω = G ω' := by
    intro ω ω' h
    funext F
    simp only [hGdef, hX ω ω' h]
    have hc := gCof_local E thr0 θ R K D Lv Bt lev upd aux0 s0 ω ω' h
    have hfr : ∀ Q, filterRound E (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) ((s0.1 : ℕ) + 1) θ Q F R =
        filterRound E (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω') ((s0.1 : ℕ) + 1) θ Q F R := fun Q =>
      Pool.P0083.filterRound_congr E ((s0.1 : ℕ) + 1) θ _ _ Q F R (fun x _ u hu => hc x u hu)
        (fun x _ u hu => hc x u hu)
    unfold Pool.P0063.Abad
    rw [hfr]
  have key := fresh_slot (qOfT K D ps p) (Sum.inr s0) p (fun c => rfl) X hX G hG
  calc _ = ∑ ω, bw2 (qOfT K D ps p) ω * G ω ((X ω).filter (fun c => ω (Sum.inr s0) c = true)) := rfl
    _ = _ := key
    _ ≤ ∑ ω, bw2 (qOfT K D ps p) ω * delta (Fintype.card ι) p R kk M0 := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
        exact abad_le E θ R M0 kk (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) hp0 hp1 hE s0.1 Tmax
          (fun i a b hab hb => hC ω i a b hab (hb.trans s0.1.2)) hR hT hM0 hk hp (X ω)
    _ = delta (Fintype.card ι) p R kk M0 := by rw [← Finset.sum_mul, sum_bw2, one_mul]

open Classical in
/-- **Good run of the generic process.** For every update rule whose increments lie in `[0, m]`, over the sampling
and filter coins, the process fails P0073's `GoodRunT` with probability at most
`NE·D·δs + NE·D·(Lt+1)·K·delta`, with `Tmax = m·NE`. -/
theorem prob_not_goodRunT_gen {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hE : Monotone E) (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {m : ℝ} (hm : 0 ≤ m)
    (hinc : ∀ ωs φ a x, 0 ≤ gInc E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a x ∧
      gInc E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a x ≤ m)
    (hR : 1 ≤ R) (hT : m * NE ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs) :
    ∑ ω : SlotT NE D Lt K → ι → Bool, bw2 (qOfT K D ps p) ω *
        (if GoodRunT E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev (ωsOfT E K D ω)
            (φOfT K D ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K) then 0 else 1)
      ≤ NE * D * δs + NE * D * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
  have hq01 : ∀ (s : SlotT NE D Lt K) (c : ι), 0 ≤ qOfT K D ps p s c ∧ qOfT K D ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOfT, hps, hp0, hp1]
  have hw : ∀ ω : SlotT NE D Lt K → ι → Bool, 0 ≤ bw2 (qOfT K D ps p) ω := fun ω =>
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
      split_ifs
      · exact (hq01 s c).1
      · linarith [(hq01 s c).2]
  have hM0' : 0 ≤ M0 := le_trans (by positivity) hM0
  have hC : ∀ (ω : SlotT NE D Lt K → ι → Bool) i a b, a ≤ b → b ≤ NE →
      0 ≤ Lint (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) i a b ∧
        Lint (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) i a b ≤ m * NE := by
    intro ω i a b hab hb
    have h := Lint_gChat_bounds E thr0 θ R K D Lv Bt lev upd aux0 (ωsOfT E K D ω) (φOfT K D ω)
      (hinc (ωsOfT E K D ω) (φOfT K D ω)) i a b hab
    refine ⟨h.1, h.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hm
    exact_mod_cast (show b - a ≤ NE by omega)
  let P : ((Fin NE × Fin D) ⊕ (Fin NE × Fin D × Fin (Lt + 1) × Fin K)) → (SlotT NE D Lt K → ι → Bool) → Prop :=
    fun b ω => badEv E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev M0 s0 b ω
  have hpt : ∀ ω, (if GoodRunT E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev
      (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K) then (0 : ℝ) else 1) ≤
      ∑ b, if P b ω then 1 else 0 := by
    intro ω
    by_cases hg : GoodRunT E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev
        (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
    · rw [if_pos hg]; exact Finset.sum_nonneg fun b _ => by split_ifs <;> norm_num
    · rw [if_neg hg]
      have : ∃ b, P b ω := by
        by_contra hno
        push Not at hno
        exact hg (goodRunT_of_noBad E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev M0
          hD hLv hlev ω s0 hlevLt hR hM0' (fun a r => hno (Sum.inl (a, r))) (fun s => hno (Sum.inr s)))
      obtain ⟨b, hb⟩ := this
      calc (1 : ℝ) = if P b ω then 1 else 0 := by rw [if_pos hb]
        _ ≤ ∑ b, if P b ω then 1 else 0 :=
            Finset.single_le_sum (f := fun b => if P b ω then (1:ℝ) else 0)
              (fun b _ => by split_ifs <;> norm_num) (Finset.mem_univ b)
  calc _ ≤ ∑ ω : SlotT NE D Lt K → ι → Bool, bw2 (qOfT K D ps p) ω *
          ∑ b, (if P b ω then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw ω)
    _ = ∑ b, ∑ ω, bw2 (qOfT K D ps p) ω * (if P b ω then 1 else 0) := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ = ∑ ar : Fin NE × Fin D, ∑ ω, bw2 (qOfT K D ps p) ω * (if P (Sum.inl ar) ω then 1 else 0) +
          ∑ sl : Fin NE × Fin D × Fin (Lt + 1) × Fin K, ∑ ω, bw2 (qOfT K D ps p) ω *
            (if P (Sum.inr sl) ω then 1 else 0) := Fintype.sum_sum_type _
    _ ≤ ∑ _ar : Fin NE × Fin D, δs +
          ∑ _s : Fin NE × Fin D × Fin (Lt + 1) × Fin K, delta (Fintype.card ι) p R kk M0 := by
        apply add_le_add
        · refine Finset.sum_le_sum fun ar _ => le_of_eq_of_le ?_
            (sample_slot_le_T E thr0 K D (Lt := Lt) hps hp0 hp1 s0 δs hs ar.1 ar.2)
          exact Finset.sum_congr rfl fun ω _ => by congr 1; exact if_congr Iff.rfl rfl rfl
        · refine Finset.sum_le_sum fun sl _ => le_of_eq_of_le ?_
            (iter_slot_le_gen E thr0 θ R K D Lv Bt lev upd aux0 M0 kk hps hp0 hp1 hE (m * NE) hC hR hT hM0 hk hp sl)
          exact Finset.sum_congr rfl fun ω _ => by congr 1
    _ = NE * D * δs + NE * D * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, Fintype.card_prod,
          Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring

open Classical in
/-- **The generic process's start pools stay small.** For every update rule with increments in `[0, m]`, except with
probability `≤ NE·D·δs + NE·D·(Lt+1)·K·delta` over the sampling and filter coins, at every unit `a < NE` the
start-pool members number at most `D·((s0 + D·Lv·S) + (Lv−1)·S) + D·s0` (P0109's `prob_members_large_FO`). -/
theorem prob_members_large_gen {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hE : Monotone E) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {m : ℝ} (hm : 0 ≤ m)
    (hinc : ∀ ωs φ a x, 0 ≤ gInc E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a x ∧
      gInc E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a x ≤ m)
    (hR : 1 ≤ R) (hT : m * NE ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S : ℝ) (hM0S : M0 ≤ S) (hS0 : 0 ≤ S)
    (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * (S + (s0 + D * Lv * S)) ≤ S) :
    ∑ ω : SlotT NE D Lt K → ι → Bool, bw2 (qOfT K D ps p) ω *
        (if ∀ a < NE, ((members D Lv (startPools E thr0 D Lv Bt (ωsOfT E K D ω) a
            (gRun E thr0 θ R K D Lv Bt lev upd aux0 (ωsOfT E K D ω) (φOfT K D ω) a).pools)).card : ℝ) ≤
              D * ((s0 + D * Lv * S) + (Lv - 1 : ℕ) * S) + D * s0
          then 0 else 1)
      ≤ NE * D * δs + NE * D * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
  have hq01 : ∀ (s : SlotT NE D Lt K) (c : ι), 0 ≤ qOfT K D ps p s c ∧ qOfT K D ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOfT, hps, hp0, hp1]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hρ0 : 0 ≤ (1 - 1 / (4 * R : ℝ)) ^ K := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  refine le_trans (Finset.sum_le_sum fun ω _ => ?_)
    (prob_not_goodRunT_gen E thr0 θ R K D Lv Bt lev upd aux0 M0 kk hps hp0 hp1 hE hB.hD hLv hlev hm hinc hR hT
      hM0 hk hp hlevLt s0 δs hs)
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
    split_ifs
    · exact (hq01 s c).1
    · linarith [(hq01 s c).2])
  by_cases hg : GoodRunT E thr0 (gCof E thr0 θ R K D Lv Bt lev upd aux0 ω) θ R K D Lv Bt lev (ωsOfT E K D ω)
      (φOfT K D ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
  · rw [if_pos]
    · split_ifs <;> norm_num
    intro a ha
    have hcard := tpools_card_le hB hLv hlev _ _ NE s0 M0 _ S hρ0 hg hM0S hS0 hρS a ha.le
    have hpe := gRun_pools_eq E thr0 θ R K D Lv Bt lev upd aux0 (ωsOfT E K D ω) (φOfT K D ω) a
    rw [hpe]
    exact members_startPools_card_le E thr0 D Lv Bt _ a _ s0 S (s0 + D * Lv * S) hcard.1 hcard.2.1
      (fun r hr hd => hg.1 a ha r hr hd)
  · rw [if_neg hg]; split_ifs <;> norm_num

end Prob

end Pool.P0156
