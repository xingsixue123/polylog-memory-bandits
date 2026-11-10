import Pool.P0073.Size
import Pool.P0063.GoodRunProb

/-!
# Probability of a good run of the threaded process (the thread analogue of P0063)
-/

namespace Pool.P0073

open Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0046

section Congr

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {C : ι → ℕ → ℝ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

/-- The pools at boundary `a` read only the filter bits of units `< a`. -/
theorem tpools_congr (ωs : ι → Bool) (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a, (∀ r, ∀ a' < a, φ r a' = φ' r a') →
      tpools E thr0 C θ R K D Lv Bt lev ωs φ a = tpools E thr0 C θ R K D Lv Bt lev ωs φ' a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    funext r
    simp only [tpools]
    rw [ih (fun r a' ha' => h r a' (by omega))]
    split_ifs
    · exact Pool.P0063.mergeUpTo_congr E C θ R K (φ r) (φ' r) a (lev r a)
        (fun ℓ _ => by rw [h r a (by omega)]) _
    · rfl

end Congr


/-- Slots of the coin array: one sampling slot per unit, one filter slot per (unit, thread, level,
iteration). -/
abbrev SlotT (NE D Lt K : ℕ) := Fin NE ⊕ (Fin NE × Fin D × Fin (Lt + 1) × Fin K)

section Model

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) {NE Lt : ℕ}

/-- Probabilities: `ps` on sampling slots, `p` on filter slots. -/
def qOfT (ps p : ℝ) : SlotT NE D Lt K → ι → ℝ
  | Sum.inl _, _ => ps
  | Sum.inr _, _ => p

/-- Sampling coins read off the array. -/
def ωsOfT (ω : SlotT NE D Lt K → ι → Bool) (c : ι) : Bool :=
  if h : E c < NE then ω (Sum.inl ⟨E c, h⟩) c else false

/-- Filter coins read off the array (`false` outside it). -/
def φOfT (ω : SlotT NE D Lt K → ι → Bool) (r a ℓ : ℕ) (k : Fin K) (c : ι) : Bool :=
  if h : a < NE ∧ r < D ∧ ℓ < Lt + 1 then ω (Sum.inr (⟨a, h.1⟩, ⟨r, h.2.1⟩, ⟨ℓ, h.2.2⟩, k)) c
  else false

variable {E thr0 C θ R K D Lv Bt lev}

theorem φOfT_eq (ω : SlotT NE D Lt K → ι → Bool) (a : Fin NE) (r : Fin D) (ℓ : Fin (Lt + 1))
    (k : Fin K) : φOfT K D ω r a ℓ k = ω (Sum.inr (a, r, ℓ, k)) := by
  funext c; simp [φOfT, a.2, r.2, ℓ.2]

theorem φOfT_agree (ω ω' : SlotT NE D Lt K → ι → Bool) (s0 : Fin NE × Fin D × Fin (Lt + 1) × Fin K)
    (h : ∀ s, s ≠ Sum.inr s0 → ω s = ω' s) (r a ℓ : ℕ) (k : Fin K)
    (hne : ¬ (a = s0.1.val ∧ r = s0.2.1.val ∧ ℓ = s0.2.2.1.val ∧ k = s0.2.2.2)) :
    φOfT K D ω r a ℓ k = φOfT K D ω' r a ℓ k := by
  funext c
  unfold φOfT
  split_ifs with hh
  · rw [h]
    intro heq
    apply hne
    have h' := Sum.inr_injective heq
    simp only [Prod.ext_iff] at h'
    exact ⟨congrArg Fin.val h'.1, congrArg Fin.val h'.2.1, congrArg Fin.val h'.2.2.1, h'.2.2.2⟩
  · rfl

theorem ωsOfT_agree (ω ω' : SlotT NE D Lt K → ι → Bool) (s0 : Fin NE × Fin D × Fin (Lt + 1) × Fin K)
    (h : ∀ s, s ≠ Sum.inr s0 → ω s = ω' s) : ωsOfT E K D ω = ωsOfT E K D ω' := by
  funext c
  unfold ωsOfT
  split_ifs with hh
  · rw [h _ (by simp)]
  · rfl

variable (E thr0 C θ R K D Lv Bt lev)

/-- The input of the merge of level `ℓ` of thread `r` at the end of unit `a`. -/
noncomputable def mergeInT (ω : SlotT NE D Lt K → ι → Bool) (a r ℓ : ℕ) : Finset ι :=
  stage E C θ R K (φOfT K D ω r) a (startPools E thr0 D Lv Bt (ωsOfT E K D ω) a
      (tpools E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) a) r) ℓ (ℓ + 1) ∪
    stage E C θ R K (φOfT K D ω r) a (startPools E thr0 D Lv Bt (ωsOfT E K D ω) a
      (tpools E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) a) r) ℓ ℓ

/-- The input of iteration `k` of that merge. -/
noncomputable def iterInT (ω : SlotT NE D Lt K → ι → Bool) (a r ℓ : ℕ) (k : Fin K) : Finset ι :=
  iter (mstep E C (a + 1) θ R) (mergeInT E thr0 C θ R K D Lv Bt lev ω a r ℓ) k
    (fun j => φOfT K D ω r a ℓ (Fin.castLE k.2.le j))

variable {E thr0 C θ R K D Lv Bt lev}

theorem stage_congr (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (a ℓ : ℕ) (P : ℕ → Finset ι)
    (h : ∀ ℓ' < ℓ, φ a ℓ' = φ' a ℓ') :
    stage E C θ R K φ a P ℓ = stage E C θ R K φ' a P ℓ := by
  cases ℓ with
  | zero => rfl
  | succ m =>
    simp only [stage]
    exact Pool.P0063.mergeUpTo_congr E C θ R K φ φ' a m (fun ℓ' hℓ' => h ℓ' (by omega)) P

/-- **Locality**: the input of iteration `s0` does not read the bits of slot `s0`. -/
theorem iterInT_local (s0 : Fin NE × Fin D × Fin (Lt + 1) × Fin K) (ω ω' : SlotT NE D Lt K → ι → Bool)
    (h : ∀ s, s ≠ Sum.inr s0 → ω s = ω' s) :
    iterInT E thr0 C θ R K D Lv Bt lev ω s0.1 s0.2.1 s0.2.2.1 s0.2.2.2 =
      iterInT E thr0 C θ R K D Lv Bt lev ω' s0.1 s0.2.1 s0.2.2.1 s0.2.2.2 := by
  obtain ⟨a, r, ℓ, k⟩ := s0
  have hs := ωsOfT_agree (E := E) ω ω' (a, r, ℓ, k) h
  have hφ1 : ∀ r', ∀ a' < a.val, φOfT K D ω r' a' = φOfT K D ω' r' a' := by
    intro r' a' ha'; funext ℓ' k'
    exact φOfT_agree ω ω' (a, r, ℓ, k) h r' a' ℓ' k' (by rintro ⟨h1, -⟩; simp at h1; omega)
  have hφ2 : ∀ ℓ' < ℓ.val, φOfT K D ω r a ℓ' = φOfT K D ω' r a ℓ' := by
    intro ℓ' hℓ'; funext k'
    exact φOfT_agree ω ω' (a, r, ℓ, k) h r a ℓ' k' (by rintro ⟨-, -, h3, -⟩; simp at h3; omega)
  have htp : tpools E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω') (φOfT K D ω) a =
      tpools E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω') (φOfT K D ω') a :=
    tpools_congr _ _ _ a hφ1
  unfold iterInT mergeInT
  simp only
  rw [hs, htp]
  rw [stage_congr (φOfT K D ω r) (φOfT K D ω' r) a (ℓ : ℕ) _ (fun ℓ' hℓ' => by rw [hφ2 ℓ' hℓ'])]
  congr 1
  funext j
  apply φOfT_agree ω ω' (a, r, ℓ, k) h
  rintro ⟨-, -, -, h4⟩
  have := congrArg Fin.val h4
  simp at this; omega

end Model


section Prob

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) {NE Lt : ℕ} (M0 : ℝ) (kk : ℕ)

/-- Copies in a merge iteration input at the end of unit `a` entered by `a`. -/
theorem E_le_of_mem_iterInT (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (ω : SlotT NE D Lt K → ι → Bool) (a r ℓ : ℕ) (k : Fin K) :
    ∀ c ∈ iterInT E thr0 C θ R K D Lv Bt lev ω a r ℓ k, E c ≤ a + 1 := by
  intro c hc
  have h1 := iter_sub (mstep E C (a + 1) θ R) _ (mstep_sub E C (a + 1) θ R) k _ hc
  unfold mergeInT at h1
  have hS := start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv
    (tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := C) (θ := θ) (R := R) (lev := lev)
      hD hLv hlev (ωsOfT E K D ω) (φOfT K D ω) a) (ωsOfT E K D ω) (x := a)
  have hstage : ∀ m j, c ∈ stage E C θ R K (φOfT K D ω r) a (startPools E thr0 D Lv Bt (ωsOfT E K D ω) a
      (tpools E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) a) r) m j → E c ≤ a + 1 := by
    intro m j hm
    cases m with
    | zero => exact ((hS c r j hm).1).trans (by omega)
    | succ m =>
      obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo m _ j c hm
      exact ((hS c r j' hj').1).trans (by omega)
  rcases Finset.mem_union.1 h1 with h | h
  · exact hstage _ _ h
  · exact hstage _ _ h

open Classical in
/-- One merge iteration of the threaded process is bad with probability at most P0042's `delta`. -/
theorem iter_slot_le_T {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E)
    (Tmax : ℝ) (hC : ∀ i a b, a ≤ b → b ≤ NE → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (s0 : Fin NE × Fin D × Fin (Lt + 1) × Fin K) :
    ∑ ω, bw2 (qOfT K D ps p) ω *
        (if Pool.P0063.Abad E C θ R M0 s0.1
            (iterInT E thr0 C θ R K D Lv Bt lev ω s0.1 s0.2.1 s0.2.2.1 s0.2.2.2)
            ((iterInT E thr0 C θ R K D Lv Bt lev ω s0.1 s0.2.1 s0.2.2.1 s0.2.2.2).filter
              (fun c => ω (Sum.inr s0) c = true))
          then 1 else 0) ≤ delta (Fintype.card ι) p R kk M0 := by
  have hq01 : ∀ (s : SlotT NE D Lt K) (c : ι), 0 ≤ qOfT K D ps p s c ∧ qOfT K D ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOfT, hps, hp0, hp1]
  refine fresh_slot_le (qOfT K D ps p) hq01 (Sum.inr s0) p (fun c => rfl)
    (fun ω => iterInT E thr0 C θ R K D Lv Bt lev ω s0.1 s0.2.1 s0.2.2.1 s0.2.2.2)
    (fun ω ω' h => iterInT_local s0 ω ω' h) (Pool.P0063.Abad E C θ R M0 s0.1) _ ?_
  intro Q
  by_cases hQ : ∀ i ∈ Q, E i ≤ (s0.1 : ℕ) + 1
  · have hs0NE : (s0.1 : ℕ) + 1 ≤ NE := s0.1.2
    have hL : ∀ i ∈ Q, ∀ a b, a ≤ b → b ≤ (s0.1 : ℕ) + 1 → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax :=
      fun i _ a b hab hb => hC i a b hab (hb.trans hs0NE)
    have hb := prob_bad_le E C ((s0.1 : ℕ) + 1) θ hp0 hp1 hE Q hQ Tmax hL R kk hR hT M0 hM0 hk hp
    have heq := Pool.P0063.prob_eq_subsetSum p Q (fun F => M0 ≤ Q.card ∧
      (1 - 1 / (4 * R : ℝ)) * Q.card < (filterRound E C ((s0.1 : ℕ) + 1) θ Q F R).card)
    have h2 : ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) *
        (if Pool.P0063.Abad E C θ R M0 s0.1 Q F then 1 else 0) =
        ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) *
        (if M0 ≤ Q.card ∧ (1 - 1 / (4 * R : ℝ)) * Q.card <
            (filterRound E C ((s0.1 : ℕ) + 1) θ Q F R).card then 1 else 0) := by
      apply Finset.sum_congr rfl; intro F _
      congr 1
      by_cases hc : M0 ≤ Q.card ∧ (1 - 1 / (4 * R : ℝ)) * Q.card <
          (filterRound E C ((s0.1 : ℕ) + 1) θ Q F R).card
      · rw [if_pos (show Pool.P0063.Abad E C θ R M0 s0.1 Q F from ⟨hQ, hc⟩), if_pos hc]
      · rw [if_neg (show ¬ Pool.P0063.Abad E C θ R M0 s0.1 Q F from fun h => hc h.2), if_neg hc]
    rw [h2, ← heq]
    exact hb
  · have h0 : ∀ F, ¬ Pool.P0063.Abad E C θ R M0 s0.1 Q F := fun F h => hQ h.1
    simp only [h0, if_false, mul_zero, Finset.sum_const_zero]
    exact delta_nonneg hp1

open Classical in
/-- One (unit, thread) samples more than `s0` copies with probability at most `δs`. -/
theorem sample_slot_le_T {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s0 : ℕ)
    (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs) (a : Fin NE) (r : Fin D) :
    ∑ ω : SlotT NE D Lt K → ι → Bool, bw2 (qOfT K D ps p) ω *
      (if s0 < (newAtT E thr0 (ωsOfT E K D ω) a r).card then 1 else 0) ≤ δs := by
  have hq01 : ∀ (s : SlotT NE D Lt K) (c : ι), 0 ≤ qOfT K D ps p s c ∧ qOfT K D ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOfT, hps, hp0, hp1]
  set X := Finset.univ.filter fun c => E c = (a : ℕ) ∧ thr0 c = (r : ℕ)
  have hnew : ∀ ω : SlotT NE D Lt K → ι → Bool, newAtT E thr0 (ωsOfT E K D ω) a r =
      X.filter (fun c => ω (Sum.inl a) c = true) := by
    intro ω; ext c
    unfold newAtT
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold ωsOfT
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      have hlt : E c < NE := h1 ▸ a.2
      rw [dif_pos hlt] at h3
      have : (⟨E c, hlt⟩ : Fin NE) = a := Fin.ext h1
      rwa [this] at h3
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, ?_⟩
      have hlt : E c < NE := h1 ▸ a.2
      rw [dif_pos hlt]
      have : (⟨E c, hlt⟩ : Fin NE) = a := Fin.ext h1
      rwa [this]
  simp only [hnew]
  have key := fresh_slot_le (qOfT K D ps p) hq01 (Sum.inl a) ps (fun c => rfl)
    (fun _ => X) (fun _ _ _ => rfl)
    (fun Q F => Q = X ∧ s0 < F.card) δs
    (fun Q => by
      by_cases hQ : Q = X
      · subst hQ; simpa using hs a r a.2 r.2
      · simp only [hQ, false_and, ite_false, mul_zero, Finset.sum_const_zero]
        refine le_trans (Finset.sum_nonneg fun F _ => ?_) (hs a r a.2 r.2)
        apply mul_nonneg (mul_nonneg (pow_nonneg hps.1 _) (pow_nonneg (by linarith [hps.2]) _))
        split_ifs <;> norm_num)
  simpa using key

end Prob


section Good

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) {NE Lt : ℕ} (M0 : ℝ) (kk : ℕ)

/-- **Deterministic step**: no large sample and no bad merge iteration ⇒ a good run. -/
theorem goodRunT_of_noBad (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (ω : SlotT NE D Lt K → ι → Bool) (s0 : ℕ) (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt)
    (hR : 1 ≤ R) (hM0 : 0 ≤ M0)
    (hs : ∀ (a : Fin NE) (r : Fin D), ¬ s0 < (newAtT E thr0 (ωsOfT E K D ω) a r).card)
    (hm : ∀ s : Fin NE × Fin D × Fin (Lt + 1) × Fin K,
      ¬ Pool.P0063.Abad E C θ R M0 s.1 (iterInT E thr0 C θ R K D Lv Bt lev ω s.1 s.2.1 s.2.2.1 s.2.2.2)
        ((iterInT E thr0 C θ R K D Lv Bt lev ω s.1 s.2.1 s.2.2.1 s.2.2.2).filter
          (fun c => ω (Sum.inr s) c = true))) :
    GoodRunT E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0
      ((1 - 1 / (4 * R : ℝ)) ^ K) := by
  classical
  refine ⟨fun a ha r hr _ => not_lt.mp (hs ⟨a, ha⟩ ⟨r, hr⟩), ?_⟩
  intro a ha r hr _ ℓ hℓ
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hε0 : 0 ≤ 1 / (4 * R : ℝ) := by positivity
  have hε1 : 1 / (4 * R : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  by_contra hbad
  have hany := mt (card_iter_le (mstep E C (a + 1) θ R) (mstep_sub E C (a + 1) θ R)
    (mergeInT E thr0 C θ R K D Lv Bt lev ω a r ℓ) M0 (1 / (4 * R : ℝ)) hM0 hε0 hε1 K
    (φOfT K D ω r a ℓ)) hbad
  obtain ⟨k, hk⟩ := Pool.P0063.exists_bad_of_anyBad _ _ _ K (φOfT K D ω r a ℓ) (not_not.mp hany)
  have hℓ' : ℓ < Lt + 1 := by have := hlevLt a ha r hr; omega
  apply hm (⟨a, ha⟩, ⟨r, hr⟩, ⟨ℓ, hℓ'⟩, k)
  have hit : iterInT E thr0 C θ R K D Lv Bt lev ω (⟨a, ha⟩ : Fin NE) (⟨r, hr⟩ : Fin D)
      (⟨ℓ, hℓ'⟩ : Fin (Lt + 1)) k =
      iter (mstep E C (a + 1) θ R) (mergeInT E thr0 C θ R K D Lv Bt lev ω a r ℓ) k
        (fun j => φOfT K D ω r a ℓ (Fin.castLE k.2.le j)) := rfl
  rw [hit]
  refine ⟨?_, hk.1, ?_⟩
  · intro i hi
    exact E_le_of_mem_iterInT E thr0 C θ R K D Lv Bt lev hD hLv hlev ω a r ℓ k i hi
  · have h2 := hk.2
    have hφ : φOfT K D ω r a ℓ k = ω (Sum.inr (⟨a, ha⟩, ⟨r, hr⟩, ⟨ℓ, hℓ'⟩, k)) :=
      φOfT_eq ω ⟨a, ha⟩ ⟨r, hr⟩ ⟨ℓ, hℓ'⟩ k
    unfold mstep at h2
    rw [hφ] at h2
    exact h2

end Good


section Union

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) {NE Lt : ℕ} (M0 : ℝ) (kk : ℕ)

/-- Bad events: a large sample of (unit, thread), or a bad merge iteration. -/
def badEv (s0 : ℕ) :
    ((Fin NE × Fin D) ⊕ (Fin NE × Fin D × Fin (Lt + 1) × Fin K)) → (SlotT NE D Lt K → ι → Bool) → Prop
  | Sum.inl ar, ω => s0 < (newAtT E thr0 (ωsOfT E K D ω) ar.1 ar.2).card
  | Sum.inr s, ω => Pool.P0063.Abad E C θ R M0 s.1
      (iterInT E thr0 C θ R K D Lv Bt lev ω s.1 s.2.1 s.2.2.1 s.2.2.2)
      ((iterInT E thr0 C θ R K D Lv Bt lev ω s.1 s.2.1 s.2.2.1 s.2.2.2).filter
        (fun c => ω (Sum.inr s) c = true))

open Classical in
/-- **Probability of a bad run of the threaded process**: at most `NE·D·δs + NE·D·(Lt+1)·K·delta`. -/
theorem prob_not_goodRunT {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hE : Monotone E) (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (Tmax : ℝ) (hC : ∀ i a b, a ≤ b → b ≤ NE → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs) :
    ∑ ω : SlotT NE D Lt K → ι → Bool, bw2 (qOfT K D ps p) ω *
        (if GoodRunT E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0
            ((1 - 1 / (4 * R : ℝ)) ^ K) then 0 else 1)
      ≤ NE * D * δs + NE * D * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
  have hq01 : ∀ (s : SlotT NE D Lt K) (c : ι), 0 ≤ qOfT K D ps p s c ∧ qOfT K D ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOfT, hps, hp0, hp1]
  have hw : ∀ ω : SlotT NE D Lt K → ι → Bool, 0 ≤ bw2 (qOfT K D ps p) ω := fun ω =>
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
      split_ifs
      · exact (hq01 s c).1
      · linarith [(hq01 s c).2]
  have hM0' : 0 ≤ M0 := le_trans (by positivity) hM0
  let P := badEv E thr0 C θ R K D Lv Bt lev (NE := NE) (Lt := Lt) M0 s0
  have hpt : ∀ ω, (if GoodRunT E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0
      ((1 - 1 / (4 * R : ℝ)) ^ K) then (0 : ℝ) else 1) ≤ ∑ b, if P b ω then 1 else 0 := by
    intro ω
    by_cases hg : GoodRunT E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0
        ((1 - 1 / (4 * R : ℝ)) ^ K)
    · rw [if_pos hg]; exact Finset.sum_nonneg fun b _ => by split_ifs <;> norm_num
    · rw [if_neg hg]
      have : ∃ b, P b ω := by
        by_contra hno
        push Not at hno
        exact hg (goodRunT_of_noBad E thr0 C θ R K D Lv Bt lev M0 hD hLv hlev ω s0 hlevLt hR hM0'
          (fun a r => hno (Sum.inl (a, r))) (fun s => hno (Sum.inr s)))
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
          ∑ s : Fin NE × Fin D × Fin (Lt + 1) × Fin K, ∑ ω, bw2 (qOfT K D ps p) ω *
            (if P (Sum.inr s) ω then 1 else 0) := Fintype.sum_sum_type _
    _ ≤ ∑ _ar : Fin NE × Fin D, δs +
          ∑ _s : Fin NE × Fin D × Fin (Lt + 1) × Fin K, delta (Fintype.card ι) p R kk M0 := by
        apply add_le_add
        · refine Finset.sum_le_sum fun ar _ => le_of_eq_of_le ?_
            (sample_slot_le_T E thr0 K D (Lt := Lt) hps hp0 hp1 s0 δs hs ar.1 ar.2)
          exact Finset.sum_congr rfl fun ω _ => by congr 1; exact if_congr Iff.rfl rfl rfl
        · refine Finset.sum_le_sum fun s _ => le_of_eq_of_le ?_
            (iter_slot_le_T E thr0 C θ R K D Lv Bt lev M0 kk hps hp0 hp1 hE Tmax hC hR hT hM0 hk hp s)
          exact Finset.sum_congr rfl fun ω _ => by congr 1
    _ = NE * D * δs + NE * D * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, Fintype.card_prod,
          Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring

open Classical in
/-- **Pool sizes of the threaded process, with probability**: except with probability
`≤ NE·D·δs + NE·D·(Lt+1)·K·delta`, at every boundary `a ≤ NE` every level `≥ 1` has at most `S`
copies and level 0 at most `s0 + D·Lv·S`. -/
theorem prob_tpools_large_le {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hE : Monotone E) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (Tmax : ℝ) (hC : ∀ i a b, a ≤ b → b ≤ NE → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S : ℝ) (hM0S : M0 ≤ S) (hS0 : 0 ≤ S)
    (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * (S + (s0 + D * Lv * S)) ≤ S) :
    ∑ ω : SlotT NE D Lt K → ι → Bool, bw2 (qOfT K D ps p) ω *
        (if ∀ a ≤ NE, (∀ r ℓ, ℓ ≠ 0 →
            ((tpools E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) a r ℓ).card : ℝ) ≤ S) ∧
            (∀ r, ((tpools E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) a r 0).card : ℝ) ≤
              s0 + D * Lv * S)
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
    (prob_not_goodRunT E thr0 C θ R K D Lv Bt lev M0 kk hps hp0 hp1 hE hB.hD hLv hlev Tmax hC hR hT hM0
      hk hp hlevLt s0 δs hs)
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
    split_ifs
    · exact (hq01 s c).1
    · linarith [(hq01 s c).2])
  by_cases hg : GoodRunT E thr0 C θ R K D Lv Bt lev (ωsOfT E K D ω) (φOfT K D ω) NE s0 M0
      ((1 - 1 / (4 * R : ℝ)) ^ K)
  · rw [if_pos (fun a ha => ⟨(tpools_card_le hB hLv hlev _ _ NE s0 M0 _ S hρ0 hg hM0S hS0 hρS a ha).1,
      (tpools_card_le hB hLv hlev _ _ NE s0 M0 _ S hρ0 hg hM0S hS0 hρS a ha).2.1⟩)]
    split_ifs <;> norm_num
  · rw [if_neg hg]; split_ifs <;> norm_num

end Union

end Pool.P0073
