import Pool.P0095.FOProc
import Pool.P0073.Prob

/-!
# Good runs of the one-free-observation threaded process, with adapted cover data

P0073 bounds the pool sizes of P0065's threaded process with probability, for cover data `C` FIXED in advance.
P0095's one-free-observation process merges with its OWN realized estimates `Chat`, which depend on the sampling and
filter coins. This file shows that P0073's bound still holds, for every fixed slot sequence `y`:

* `foRun_congr_φ`, `Chat_congr_φ`: the state at boundary `a` reads only the filter bits of units `< a`; the
  estimates up to time `a + 1` too (the merges at the end of unit `a` come after its observation).
* `stage_congrC`, `iterInT_congrC`: a merge iteration at the end of unit `a` reads the cover data only up to `a + 1`.
* `Cof` (the estimates on P0073's coin array) and `Cof_local`: they do not read the filter bits of any iteration
  of unit `a` up to time `a + 1`.
* `Lint_Chat_bounds`: with losses in `[0, 1]`, estimate increments lie in `[0, s·len]`.
* `abad_le`: P0042's per-input merge bound for any data with bounded increments (extracted from P0073).
* `iter_slot_le_FO`: one merge iteration is bad with probability `≤ delta`, via P0046's `fresh_slot` with a
  coin-dependent integrand.
* `prob_not_goodRunT_FO`: `P(not GoodRunT) ≤ NE·D·δs + NE·D·(Lt+1)·K·delta` with `Tmax = s·NE`.
* `mem_inherit_sub`, `members_startPools_sub`, `members_startPools_card_le`: the start-pool members (what the slots
  must hold) are counted from the boundary pool sizes and the new samples.
* `prob_members_large_FO`: except with that probability, at every unit `a < NE` the start-pool members number at most
  `D·((s0 + D·Lv·S) + (Lv−1)·S) + D·s0`.
-/

namespace Pool.P0109

open Finset Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0046 Pool.P0073

section Local

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι) (ωs : ι → Bool) (y : ℕ → Fin s)

/-- **Locality in the filter bits.** The state at boundary `a` reads only the filter bits of units `< a`. -/
theorem foRun_congr_φ {φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool} : ∀ a, (∀ r, ∀ a' < a, φ r a' = φ' r a') →
    foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a = foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ' y a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have ih' := ih (fun r a' ha' => h r a' (by omega))
    simp only [foRun]
    rw [ih']
    congr 1
    funext r
    split_ifs
    · exact Pool.P0063.mergeUpTo_congr E _ θ R K (φ r) (φ' r) a (lev r a)
        (fun ℓ _ => by rw [h r a (by omega)]) _
    · rfl

/-- The realized estimates up to time `a + 1` read only the filter bits of units `< a` (the merges at the end of
unit `a` come after its observation). -/
theorem Chat_congr_φ {φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool} (a : ℕ) (h : ∀ r, ∀ a' < a, φ r a' = φ' r a')
    (x : ι) (t : ℕ) (ht : t ≤ a + 1) :
    Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x t = Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ' y x t := by
  rcases Nat.lt_or_eq_of_le ht with ht | ht
  · unfold Chat
    rw [foRun_congr_φ E thr0 θ R K D Lv Bt lev s L occ ωs y t (fun r a' ha' => h r a' (by omega))]
  · subst ht
    have hf := foRun_congr_φ E thr0 θ R K D Lv Bt lev s L occ ωs y a h
    rw [Chat_succ, Chat_succ]
    have h1 : Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x a = Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ' y x a := by
      unfold Chat; rw [hf]
    unfold obsAt; rw [hf, h1]

end Local

section CongrC

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) {NE Lt : ℕ}

theorem stage_congrC (C C' : ι → ℕ → ℝ) (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) (P : ℕ → Finset ι)
    (hC : ∀ x u, u ≤ a + 1 → C x u = C' x u) (m : ℕ) :
    stage E C θ R K φ a P m = stage E C' θ R K φ a P m := by
  cases m with
  | zero => rfl
  | succ m =>
    simp only [stage]
    exact Pool.P0083.mergeUpTo_congr E θ R K C C' φ a P (fun j x _ u hu => hC x u hu) m

/-- The input of a merge iteration at the end of unit `a` reads the cover data only up to time `a + 1`. -/
theorem iterInT_congrC {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (C C' : ι → ℕ → ℝ)
    (ω : SlotT NE D Lt K → ι → Bool) (a r ℓ : ℕ) (k : Fin K) (hC : ∀ x u, u ≤ a + 1 → C x u = C' x u) :
    iterInT E thr0 C θ R K D Lv Bt lev ω a r ℓ k = iterInT E thr0 C' θ R K D Lv Bt lev ω a r ℓ k := by
  have htp : tpools E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) a =
      tpools E thr0 C' θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) a :=
    Pool.P0083.tpools_congr E thr0 θ R K D Lv Bt lev C C' _ _ a (fun x _ u hu => hC x u (by omega))
  unfold iterInT mergeInT
  rw [htp, stage_congrC E θ R K C C' _ a _ hC ℓ]
  exact Pool.P0083.iter_congr E (a + 1) θ R C C' _ (fun x _ u hu => hC x u hu) _ _

end CongrC

section Bounds

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s)

/-- With losses in `[0, 1]`, the realized estimates grow by at most `s` per unit. -/
theorem Lint_Chat_bounds (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (i : ι) (a : ℕ) :
    ∀ b, a ≤ b → 0 ≤ Lint (Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y) i a b ∧
      Lint (Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y) i a b ≤ s * ((b - a : ℕ) : ℝ) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp [Lint]
  | succ b hab ih =>
    have hstep := Chat_succ E thr0 θ R K D Lv Bt lev s L occ ωs φ y i b
    have hinc : 0 ≤ (if obsAt E thr0 θ R K D Lv Bt lev s L occ ωs φ y b = some i then (s : ℝ) * L b i else 0) ∧
        (if obsAt E thr0 θ R K D Lv Bt lev s L occ ωs φ y b = some i then (s : ℝ) * L b i else 0) ≤ s := by
      split_ifs
      · exact ⟨mul_nonneg (Nat.cast_nonneg s) (hL0 b i), mul_le_of_le_one_right (Nat.cast_nonneg s) (hL1 b i)⟩
      · exact ⟨le_rfl, Nat.cast_nonneg s⟩
    unfold Lint at ih ⊢
    rw [hstep]
    have hcast : ((b + 1 - a : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) + 1 := by
      rw [show b + 1 - a = (b - a) + 1 by omega]; push_cast; ring
    rw [hcast]
    constructor <;> nlinarith [ih.1, ih.2, hinc.1, hinc.2]

end Bounds

section Prob

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) {NE Lt : ℕ}
  (M0 : ℝ) (kk : ℕ)

/-- The cover data of the FO process on the coin array `ω` (slots `y` fixed): its realized estimates. -/
noncomputable def Cof (ω : SlotT NE D Lt K → ι → Bool) : ι → ℕ → ℝ :=
  Chat E thr0 θ R K D Lv Bt lev s L occ (ωsOfT E K D ω) (φOfT K D ω) y

/-- The data read by a merge iteration do not read its own filter bits. -/
theorem Cof_local (s0 : Fin NE × Fin D × Fin (Lt + 1) × Fin K) (ω ω' : SlotT NE D Lt K → ι → Bool)
    (h : ∀ s, s ≠ Sum.inr s0 → ω s = ω' s) :
    ∀ x u, u ≤ (s0.1 : ℕ) + 1 → Cof E thr0 θ R K D Lv Bt lev s L occ y ω x u =
      Cof E thr0 θ R K D Lv Bt lev s L occ y ω' x u := by
  intro x u hu
  unfold Cof
  rw [ωsOfT_agree (E := E) ω ω' s0 h]
  refine Chat_congr_φ E thr0 θ R K D Lv Bt lev s L occ _ y (s0.1 : ℕ) (fun r a' ha' => ?_) x u hu
  funext ℓ k
  exact φOfT_agree ω ω' s0 h r a' ℓ k (by rintro ⟨h1, -⟩; omega)

open Classical in
/-- P0042's merge bound for one input set, for any data with bounded increments. -/
theorem abad_le (C : ι → ℕ → ℝ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E) (a : ℕ) (Tmax : ℝ)
    (hC : ∀ i a' b, a' ≤ b → b ≤ a + 1 → 0 ≤ Lint C i a' b ∧ Lint C i a' b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (Q : Finset ι) :
    ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) *
      (if Pool.P0063.Abad E C θ R M0 a Q F then 1 else 0) ≤ delta (Fintype.card ι) p R kk M0 := by
  by_cases hQ : ∀ i ∈ Q, E i ≤ a + 1
  · have hL : ∀ i ∈ Q, ∀ a' b, a' ≤ b → b ≤ a + 1 → 0 ≤ Lint C i a' b ∧ Lint C i a' b ≤ Tmax :=
      fun i _ a' b hab hb => hC i a' b hab hb
    have hb := prob_bad_le E C (a + 1) θ hp0 hp1 hE Q hQ Tmax hL R kk hR hT M0 hM0 hk hp
    have heq := Pool.P0063.prob_eq_subsetSum p Q (fun F => M0 ≤ Q.card ∧
      (1 - 1 / (4 * R : ℝ)) * Q.card < (filterRound E C (a + 1) θ Q F R).card)
    have h2 : ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) *
        (if Pool.P0063.Abad E C θ R M0 a Q F then 1 else 0) =
        ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) *
        (if M0 ≤ Q.card ∧ (1 - 1 / (4 * R : ℝ)) * Q.card <
            (filterRound E C (a + 1) θ Q F R).card then 1 else 0) := by
      apply Finset.sum_congr rfl; intro F _
      congr 1
      by_cases hc : M0 ≤ Q.card ∧ (1 - 1 / (4 * R : ℝ)) * Q.card < (filterRound E C (a + 1) θ Q F R).card
      · rw [if_pos (show Pool.P0063.Abad E C θ R M0 a Q F from ⟨hQ, hc⟩), if_pos hc]
      · rw [if_neg (show ¬ Pool.P0063.Abad E C θ R M0 a Q F from fun h => hc h.2), if_neg hc]
    rw [h2, ← heq]
    exact hb
  · have h0 : ∀ F, ¬ Pool.P0063.Abad E C θ R M0 a Q F := fun F h => hQ h.1
    simp only [h0, if_false, mul_zero, Finset.sum_const_zero]
    exact delta_nonneg hp1

open Classical in
/-- **One merge iteration of the FO process is bad with probability at most `delta`**, although its cover data
(the realized estimates) depend on the coins: they do not read the iteration's own filter bits. -/
theorem iter_slot_le_FO {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E)
    (Tmax : ℝ) (hC : ∀ (ω : SlotT NE D Lt K → ι → Bool) i a b, a ≤ b → b ≤ NE →
      0 ≤ Lint (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) i a b ∧
        Lint (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) i a b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (s0 : Fin NE × Fin D × Fin (Lt + 1) × Fin K) :
    ∑ ω, bw2 (qOfT K D ps p) ω *
        (if Pool.P0063.Abad E (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R M0 s0.1
            (iterInT E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev ω
              s0.1 s0.2.1 s0.2.2.1 s0.2.2.2)
            ((iterInT E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev ω
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
    iterInT E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev ω s0.1 s0.2.1 s0.2.2.1 s0.2.2.2
    with hXdef
  have hX : ∀ ω ω', (∀ s, s ≠ Sum.inr s0 → ω s = ω' s) → X ω = X ω' := by
    intro ω ω' h
    simp only [hXdef]
    rw [iterInT_congrC θ R K D Lv Bt lev E thr0 _ _ ω _ _ _ _
      (fun x u hu => Cof_local E thr0 θ R K D Lv Bt lev s L occ y s0 ω ω' h x u hu)]
    exact iterInT_local s0 ω ω' h
  set G : (SlotT NE D Lt K → ι → Bool) → Finset ι → ℝ := fun ω F =>
    if Pool.P0063.Abad E (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R M0 s0.1 (X ω) F then 1 else 0 with hGdef
  have hG : ∀ ω ω', (∀ s, s ≠ Sum.inr s0 → ω s = ω' s) → G ω = G ω' := by
    intro ω ω' h
    funext F
    simp only [hGdef, hX ω ω' h]
    have hc := Cof_local E thr0 θ R K D Lv Bt lev s L occ y s0 ω ω' h
    have hfr : ∀ Q, filterRound E (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) ((s0.1 : ℕ) + 1) θ Q F R =
        filterRound E (Cof E thr0 θ R K D Lv Bt lev s L occ y ω') ((s0.1 : ℕ) + 1) θ Q F R := fun Q =>
      Pool.P0083.filterRound_congr E ((s0.1 : ℕ) + 1) θ _ _ Q F R (fun x _ u hu => hc x u hu)
        (fun x _ u hu => hc x u hu)
    unfold Pool.P0063.Abad
    rw [hfr]
  have key := fresh_slot (qOfT K D ps p) (Sum.inr s0) p (fun c => rfl) X hX G hG
  calc _ = ∑ ω, bw2 (qOfT K D ps p) ω * G ω ((X ω).filter (fun c => ω (Sum.inr s0) c = true)) := rfl
    _ = _ := key
    _ ≤ ∑ ω, bw2 (qOfT K D ps p) ω * delta (Fintype.card ι) p R kk M0 := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
        exact abad_le E θ R M0 kk (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) hp0 hp1 hE s0.1 Tmax
          (fun i a b hab hb => hC ω i a b hab (hb.trans s0.1.2)) hR hT hM0 hk hp (X ω)
    _ = delta (Fintype.card ι) p R kk M0 := by rw [← Finset.sum_mul, sum_bw2, one_mul]

end Prob

section Union

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) {NE Lt : ℕ}
  (M0 : ℝ) (kk : ℕ)

open Classical in
/-- **Good run of the FO process, with adapted cover data.** For every fixed slot sequence `y`, over the sampling
and filter coins (P0073's coin array), the FO process — whose merges use its own realized estimates — fails P0073's
`GoodRunT` with probability at most `NE·D·δs + NE·D·(Lt+1)·K·delta`, P0073's bound with `Tmax = s·NE` (losses in
`[0, 1]`). -/
theorem prob_not_goodRunT_FO {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hE : Monotone E) (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (hR : 1 ≤ R) (hT : (s : ℝ) * NE ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs) :
    ∑ ω : SlotT NE D Lt K → ι → Bool, bw2 (qOfT K D ps p) ω *
        (if GoodRunT E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev (ωsOfT E K D ω)
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
      0 ≤ Lint (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) i a b ∧
        Lint (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) i a b ≤ s * NE := by
    intro ω i a b hab hb
    have h := Lint_Chat_bounds E thr0 θ R K D Lv Bt lev s L occ (ωsOfT E K D ω) (φOfT K D ω) y hL0 hL1 i a b hab
    refine ⟨h.1, h.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s)
    exact_mod_cast (show b - a ≤ NE by omega)
  let P : ((Fin NE × Fin D) ⊕ (Fin NE × Fin D × Fin (Lt + 1) × Fin K)) → (SlotT NE D Lt K → ι → Bool) → Prop :=
    fun b ω => badEv E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev M0 s0 b ω
  have hpt : ∀ ω, (if GoodRunT E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev
      (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K) then (0 : ℝ) else 1) ≤
      ∑ b, if P b ω then 1 else 0 := by
    intro ω
    by_cases hg : GoodRunT E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev
        (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
    · rw [if_pos hg]; exact Finset.sum_nonneg fun b _ => by split_ifs <;> norm_num
    · rw [if_neg hg]
      have : ∃ b, P b ω := by
        by_contra hno
        push Not at hno
        exact hg (goodRunT_of_noBad E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev M0
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
            (iter_slot_le_FO E thr0 θ R K D Lv Bt lev s L occ y M0 kk hps hp0 hp1 hE (s * NE) hC hR hT hM0 hk hp sl)
          exact Finset.sum_congr rfl fun ω _ => by congr 1
    _ = NE * D * δs + NE * D * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, Fintype.card_prod,
          Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring

end Union

section Members

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (D Lv : ℕ) (Bt : ℕ → ℕ)

theorem mem_inherit_sub {a r ℓ : ℕ} {P : ℕ → ℕ → Finset ι} {x : ι} (hx : x ∈ inherit D Lv Bt a P r ℓ)
    (hr : r < D) (hℓ : ℓ < Lv) : ∃ r' < D, ∃ ℓ' < Lv, x ∈ P r' ℓ' := by
  unfold inherit at hx
  split_ifs at hx with h1 h2 h3
  · exact ⟨r, hr, ℓ, hℓ, hx⟩
  · rcases Finset.mem_union.1 hx with hx | hx
    · exact ⟨r, hr, 0, by omega, hx⟩
    · simp only [Finset.mem_biUnion, Finset.mem_Ioo, Finset.mem_range] at hx
      obtain ⟨r', ⟨-, hr'⟩, ℓ', hℓ', hx⟩ := hx
      exact ⟨r', hr', ℓ', hℓ', hx⟩
  · exact ⟨r, hr, ℓ, hℓ, hx⟩
  · exact absurd hx (Finset.notMem_empty x)

/-- The start pools' members are old members or new samples of threads whose epoch starts. -/
theorem members_startPools_sub (ωs : ι → Bool) (a : ℕ) (P : ℕ → ℕ → Finset ι) :
    members D Lv (startPools E thr0 D Lv Bt ωs a P) ⊆
      members D Lv P ∪ ((Finset.range D).filter (fun r => Bt r ∣ a)).biUnion (newAtT E thr0 ωs a) := by
  classical
  intro x hx
  simp only [members, Finset.mem_biUnion, Finset.mem_range] at hx
  obtain ⟨r, hr, ℓ, hℓ, hx⟩ := hx
  simp only [Finset.mem_union, members, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
  unfold startPools sample at hx
  split_ifs at hx with hs
  · rcases Finset.mem_union.1 hx with hx | hx
    · exact Or.inl (mem_inherit_sub D Lv Bt hx hr (by omega))
    · exact Or.inr ⟨r, ⟨hr, hs.2.1⟩, hx⟩
  · exact Or.inl (mem_inherit_sub D Lv Bt hx hr hℓ)

/-- **Members of the start pools, counted.** -/
theorem members_startPools_card_le (ωs : ι → Bool) (a : ℕ) (P : ℕ → ℕ → Finset ι) (s0 : ℕ) (S S' : ℝ)
    (hP1 : ∀ r ℓ, ℓ ≠ 0 → ((P r ℓ).card : ℝ) ≤ S) (hP0 : ∀ r, ((P r 0).card : ℝ) ≤ S')
    (hnew : ∀ r < D, Bt r ∣ a → (newAtT E thr0 ωs a r).card ≤ s0) :
    ((members D Lv (startPools E thr0 D Lv Bt ωs a P)).card : ℝ) ≤ D * (S' + (Lv - 1 : ℕ) * S) + D * s0 := by
  classical
  have h1 := Finset.card_le_card (members_startPools_sub E thr0 D Lv Bt ωs a P)
  have h2 := Finset.card_union_le (members D Lv P)
    (((Finset.range D).filter (fun r => Bt r ∣ a)).biUnion (newAtT E thr0 ωs a))
  have h3 : ((members D Lv P).card : ℝ) ≤ D * (S' + (Lv - 1 : ℕ) * S) := by
    have hle : (members D Lv P).card ≤ ∑ r ∈ Finset.range D, ∑ ℓ ∈ Finset.range Lv, (P r ℓ).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun r _ => Finset.card_biUnion_le)
    have hrow : ∀ r, (∑ ℓ ∈ Finset.range Lv, ((P r ℓ).card : ℝ)) ≤ S' + (Lv - 1 : ℕ) * S := by
      intro r
      rcases Nat.eq_zero_or_pos Lv with hLv | hLv
      · subst hLv
        simp only [Finset.range_zero, Finset.sum_empty, Nat.zero_sub, Nat.cast_zero, zero_mul, add_zero]
        exact le_trans (Nat.cast_nonneg _) (hP0 r)
      · rw [show Lv = (Lv - 1) + 1 by omega, Finset.sum_range_succ']
        simp only [Nat.add_sub_cancel]
        have : ∑ i ∈ Finset.range (Lv - 1), ((P r (i + 1)).card : ℝ) ≤ ∑ _i ∈ Finset.range (Lv - 1), S :=
          Finset.sum_le_sum fun i _ => hP1 r (i + 1) (by omega)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
        linarith [hP0 r]
    calc ((members D Lv P).card : ℝ) ≤ ∑ r ∈ Finset.range D, ∑ ℓ ∈ Finset.range Lv, ((P r ℓ).card : ℝ) := by
          exact_mod_cast hle
      _ ≤ ∑ _r ∈ Finset.range D, (S' + (Lv - 1 : ℕ) * S) := Finset.sum_le_sum fun r _ => hrow r
      _ = D * (S' + (Lv - 1 : ℕ) * S) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4 : ((((Finset.range D).filter (fun r => Bt r ∣ a)).biUnion (newAtT E thr0 ωs a)).card : ℝ) ≤ D * s0 := by
    have hle := Finset.card_biUnion_le (s := (Finset.range D).filter (fun r => Bt r ∣ a)) (t := newAtT E thr0 ωs a)
    have hle2 : ∑ r ∈ (Finset.range D).filter (fun r => Bt r ∣ a), (newAtT E thr0 ωs a r).card ≤
        ∑ _r ∈ Finset.range D, s0 := by
      refine (Finset.sum_le_sum fun r hr => ?_).trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      exact hnew r hr.1 hr.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle2
    exact_mod_cast hle.trans hle2
  have : ((members D Lv (startPools E thr0 D Lv Bt ωs a P)).card : ℝ) ≤
      (members D Lv P).card + (((Finset.range D).filter (fun r => Bt r ∣ a)).biUnion (newAtT E thr0 ωs a)).card := by
    exact_mod_cast h1.trans h2
  linarith

end Members

section Overflow

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) {NE Lt : ℕ}
  (M0 : ℝ) (kk : ℕ)

open Classical in
/-- **The FO process's start pools stay small, with adapted cover data.** For every fixed slot sequence `y`, except
with probability `≤ NE·D·δs + NE·D·(Lt+1)·K·delta` over the sampling and filter coins, at every unit `a < NE` the
start-pool members number at most `D·((s0 + D·Lv·S) + (Lv−1)·S) + D·s0`. So with at least that many slots, nothing
overflows. -/
theorem prob_members_large_FO {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hE : Monotone E) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (hR : 1 ≤ R) (hT : (s : ℝ) * NE ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
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
            (foRun E thr0 θ R K D Lv Bt lev s L occ (ωsOfT E K D ω) (φOfT K D ω) y a).pools)).card : ℝ) ≤
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
    (prob_not_goodRunT_FO E thr0 θ R K D Lv Bt lev s L occ y M0 kk hps hp0 hp1 hE hB.hD hLv hlev hL0 hL1 hR hT
      hM0 hk hp hlevLt s0 δs hs)
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
    split_ifs
    · exact (hq01 s c).1
    · linarith [(hq01 s c).2])
  by_cases hg : GoodRunT E thr0 (Cof E thr0 θ R K D Lv Bt lev s L occ y ω) θ R K D Lv Bt lev (ωsOfT E K D ω)
      (φOfT K D ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
  · rw [if_pos]
    · split_ifs <;> norm_num
    intro a ha
    have hcard := tpools_card_le hB hLv hlev _ _ NE s0 M0 _ S hρ0 hg hM0S hS0 hρS a ha.le
    have hpe := foRun_pools_eq E thr0 θ R K D Lv Bt lev s L occ (ωsOfT E K D ω) (φOfT K D ω) y a
    rw [hpe]
    exact members_startPools_card_le E thr0 D Lv Bt _ a _ s0 S (s0 + D * Lv * S) hcard.1 hcard.2.1
      (fun r hr hd => hg.1 a ha r hr hd)
  · rw [if_neg hg]; split_ifs <;> norm_num

end Overflow

end Pool.P0109
