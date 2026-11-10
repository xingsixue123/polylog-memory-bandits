import Pool.P0230.Corr

/-!
# Bounds on the twin's integers and a finite encoding

* P0102's integer run with losses `b ≤ Bm`: the grid increment is `≤ ⌊η'·Bm/ε⌋₊`, so `kL u ≤ u·⌊η'·Bm/ε⌋₊`, and the
  stored pairs satisfy `C ≤ u·Bm`, `kw ≤ kL u`.
* The twin's integer IX losses are `≤ Bm = ⌊G/(wE·γ)⌋₊`.
* A finite state `FS`: capped learner time and grid index, and a finset of at most `S` entries
  (expert, per-level capped pairs). `dec`/`enc`, and `dec (enc τ)` agrees with `τ` on everything the twin reads
  when nothing is capped. `card FS ≤ (KM+1)(KLM+1)(card X + 1)^S`.
-/

namespace Pool.P0236

open Pool.P0230 Real Finset Pool.P0019 Pool.P0089 Pool.P0102 Pool.P0212

section bounds

variable {κ : Type} [Fintype κ] [DecidableEq κ] {L : ℕ} {pr : ℕ → Finset κ} {b : ℕ → κ → ℕ} {η ε : ℝ}
  {kL : ℕ → ℕ} {lw : ℕ → κ → ℕ → ℕ × ℕ}

/-- The log mass ratio of a round with losses `≤ Bm` is `≤ η·Bm`. -/
theorem logRatio_le' {Bm u : ℕ} (hb : ∀ f, b u f ≤ Bm) (hη : 0 ≤ η) (hne : (pr u).Nonempty) :
    log (mA L pr η ε kL lw u / mA' L pr b η ε kL lw u) ≤ η * Bm := by
  have hA := mA_pos (η := η) (ε := ε) (kL := kL) (lw := lw) (L := L) hne
  have hA' := mA'_pos (b := b) (η := η) (ε := ε) (kL := kL) (lw := lw) (L := L) hne
  rw [log_le_iff_le_exp (div_pos hA hA'), div_le_iff₀ hA']
  have h : exp (-(η * Bm)) * mA L pr η ε kL lw u ≤ mA' L pr b η ε kL lw u := by
    unfold mA' mA
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ℓ _ => ?_
    have : exp (-(η * Bm)) ≤ exp (-η * (b u f : ℝ)) := by
      rw [exp_le_exp]
      have : (b u f : ℝ) ≤ Bm := by exact_mod_cast hb f
      nlinarith
    have := mw_pos (η := η) (ε := ε) (kL := kL) (lw := lw) u f ℓ
    nlinarith
  have : exp (η * Bm) * exp (-(η * Bm)) = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos (η * Bm)]

/-- The grid increment of a round with losses `≤ Bm` is `≤ ⌊η·Bm/ε⌋₊`. -/
theorem inc_le' {Bm : ℕ} {u : ℕ} (hb : ∀ f, b u f ≤ Bm) (hη : 0 ≤ η) (hε : 0 < ε) :
    inc L pr b η ε kL lw u ≤ ⌊η * Bm / ε⌋₊ := by
  unfold inc
  split_ifs with hne
  · apply Nat.floor_le_floor
    exact div_le_div_of_nonneg_right (logRatio_le' hb hη hne) hε.le
  · exact Nat.zero_le _

variable (L pr b η ε)

/-- **Bounds on P0102's explicit run** with losses `≤ Bm` before `u`. -/
theorem stS_le {Bm : ℕ} (hη : 0 ≤ η) (hε : 0 < ε) (u : ℕ) (hb : ∀ s < u, ∀ f, b s f ≤ Bm) :
    (stS L pr b η ε u).1 ≤ u * ⌊η * Bm / ε⌋₊ ∧
      ∀ f ℓ, ((stS L pr b η ε u).2 f ℓ).1 ≤ u * Bm ∧ ((stS L pr b η ε u).2 f ℓ).2 ≤ (stS L pr b η ε u).1 := by
  induction u with
  | zero => exact ⟨by simp [stS], fun f ℓ => by simp [stS]⟩
  | succ u ih =>
    obtain ⟨ih1, ih2⟩ := ih fun s hs => hb s (by omega)
    set s0 := stS L pr b η ε u with hs0
    have hinc : inc L pr b η ε (fun _ => s0.1) (fun _ => s0.2) u ≤ ⌊η * Bm / ε⌋₊ :=
      inc_le' (hb u (Nat.lt_succ_self u)) hη hε
    have hst : stS L pr b η ε (u + 1) = stepS (L := L) (pr := pr) (b := b) (η := η) (ε := ε) u s0 := rfl
    rw [hst]
    refine ⟨?_, fun f ℓ => ?_⟩
    · show s0.1 + inc L pr b η ε (fun _ => s0.1) (fun _ => s0.2) u ≤ (u + 1) * ⌊η * Bm / ε⌋₊
      rw [Nat.succ_mul]; omega
    · show (if f ∈ pr u ∧ ¬ 2 ^ ℓ ∣ u + 1 then ((s0.2 f ℓ).1 + b u f, (s0.2 f ℓ).2)
          else (0, s0.1 + inc L pr b η ε (fun _ => s0.1) (fun _ => s0.2) u)).1 ≤ (u + 1) * Bm ∧
        (if f ∈ pr u ∧ ¬ 2 ^ ℓ ∣ u + 1 then ((s0.2 f ℓ).1 + b u f, (s0.2 f ℓ).2)
          else (0, s0.1 + inc L pr b η ε (fun _ => s0.1) (fun _ => s0.2) u)).2 ≤
          s0.1 + inc L pr b η ε (fun _ => s0.1) (fun _ => s0.2) u
      split_ifs
      · have h1 := ih2 f ℓ
        have h2 := hb u (Nat.lt_succ_self u) f
        refine ⟨?_, ?_⟩
        · show (s0.2 f ℓ).1 + b u f ≤ (u + 1) * Bm
          rw [Nat.succ_mul]; omega
        · show (s0.2 f ℓ).2 ≤ _; omega
      · exact ⟨by simp, le_rfl⟩

end bounds

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The integer IX losses are `≤ ⌊G/(wE·γ)⌋₊`.** -/
theorem bOfP_le (N G : ℕ) {γ wE : ℝ} (hγ : 0 < γ) (hwE : 0 < wE) (p : Option ι → ℝ) (ch : Option ι) (bit : Bool)
    (f : Option ι) : bOfP N G γ wE p ch bit f ≤ ⌊(G : ℝ) / (wE * γ)⌋₊ := by
  unfold bOfP
  split_ifs
  · apply Nat.floor_le_floor
    have hpt : 0 ≤ Pool.P0179.pt N none p f := by unfold Pool.P0179.pt; positivity
    have hb : (bit.toNat : ℝ) ≤ 1 := by cases bit <;> simp
    have hden : wE * γ ≤ wE * (Pool.P0179.pt N none p f + γ) := by nlinarith
    have h1 : (bit.toNat : ℝ) / (wE * (Pool.P0179.pt N none p f + γ)) ≤ 1 / (wE * γ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right hb (le_of_lt (mul_pos hwE hγ))
      linarith
    calc (G : ℝ) * ((bit.toNat : ℝ) / (wE * (Pool.P0179.pt N none p f + γ))) ≤ G * (1 / (wE * γ)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = G / (wE * γ) := by ring
  · exact Nat.zero_le _

section enc

variable (ι) (L S KM KLM CM : ℕ)

/-- An entry: an expert and its per-level capped pairs. -/
abbrev XE := Option ι × (Fin (L + 1) → Fin (CM + 1) × Fin (KLM + 1))

/-- **The finite twin state.** -/
abbrev FS := Fin (KM + 1) × Fin (KLM + 1) × {s : Finset (XE ι L KLM CM) // s.card ≤ S}

variable {ι L S KM KLM CM}

/-- Capping a natural number. -/
def capN (M x : ℕ) : Fin (M + 1) := ⟨min x M, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem capN_val {M x : ℕ} (h : x ≤ M) : (capN M x : ℕ) = x := by simp [capN, h]

/-- Decoding. -/
def dec (φ : FS ι L S KM KLM CM) : TS ι where
  k := φ.1
  kL := φ.2.1
  ent := φ.2.2.1.image Prod.fst
  dat f ℓ := if h : ℓ < L + 1 then
      (∑ e ∈ φ.2.2.1.filter (fun e => e.1 = f), ((e.2 ⟨ℓ, h⟩).1 : ℕ),
        ∑ e ∈ φ.2.2.1.filter (fun e => e.1 = f), ((e.2 ⟨ℓ, h⟩).2 : ℕ))
    else (0, 0)

/-- The entry of an expert. -/
def entry (τ : TS ι) (f : Option ι) : XE ι L KLM CM :=
  (f, fun ℓ => (capN CM (τ.dat f ℓ).1, capN KLM (τ.dat f ℓ).2))

/-- Encoding (the entries are dropped if there are more than `S`). -/
def enc (τ : TS ι) : FS ι L S KM KLM CM :=
  (capN KM τ.k, capN KLM τ.kL,
    if h : τ.ent.card ≤ S then ⟨τ.ent.image (entry (L := L) (KLM := KLM) (CM := CM) τ),
      Finset.card_image_le.trans h⟩ else ⟨∅, by simp⟩)

/-- **Decoding an encoding recovers everything the twin reads**, when nothing is capped. -/
theorem dec_enc {τ : TS ι} (hS : τ.ent.card ≤ S) (hk : τ.k ≤ KM) (hkL : τ.kL ≤ KLM)
    (hd : ∀ f ∈ τ.ent, ∀ ℓ ≤ L, (τ.dat f ℓ).1 ≤ CM ∧ (τ.dat f ℓ).2 ≤ KLM) :
    (dec (enc (S := S) (KM := KM) (L := L) (KLM := KLM) (CM := CM) τ)).k = τ.k ∧
      (dec (enc (S := S) (KM := KM) (L := L) (KLM := KLM) (CM := CM) τ)).kL = τ.kL ∧
      ∀ f, ∀ ℓ ≤ L, lwOf (dec (enc (S := S) (KM := KM) (L := L) (KLM := KLM) (CM := CM) τ)) f ℓ = lwOf τ f ℓ := by
  have hent : (dec (enc (S := S) (KM := KM) (L := L) (KLM := KLM) (CM := CM) τ)).ent = τ.ent := by
    simp only [dec, enc, dif_pos hS, Finset.image_image]
    convert Finset.image_id (s := τ.ent)
    funext f; rfl
  refine ⟨capN_val hk, capN_val hkL, fun f ℓ hℓ => ?_⟩
  have hk' : (dec (enc (S := S) (KM := KM) (L := L) (KLM := KLM) (CM := CM) τ)).k = τ.k := capN_val hk
  have hkL' : (dec (enc (S := S) (KM := KM) (L := L) (KLM := KLM) (CM := CM) τ)).kL = τ.kL := capN_val hkL
  unfold lwOf
  rw [hent, hk', hkL']
  split_ifs with hc
  · have hf := hc.1
    have hfil : (τ.ent.image (entry (L := L) (KLM := KLM) (CM := CM) τ)).filter (fun e => e.1 = f) =
        {entry (L := L) (KLM := KLM) (CM := CM) τ f} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨g, _, rfl⟩, he⟩
        simp only [entry] at he; rw [he]
      · rintro rfl; exact ⟨⟨f, hf, rfl⟩, rfl⟩
    have hℓ' : ℓ < L + 1 := by omega
    simp only [dec, enc, dif_pos hS, dif_pos hℓ', hfil, Finset.sum_singleton, entry]
    obtain ⟨h1, h2⟩ := hd f hf ℓ hℓ
    rw [capN_val h1, capN_val h2]
  · rfl

/-- `Rel` only reads the learner time, the grid index and the data at levels `≤ L`. -/
theorem rel_congr {η ε : ℝ} {G : ℕ} {σ : AState ι} {τ τ' : TS ι} (hR : Rel η ε L G σ τ) (hk : τ'.k = τ.k)
    (hkL : τ'.kL = τ.kL) (hlw : ∀ f, ∀ ℓ ≤ L, lwOf τ' f ℓ = lwOf τ f ℓ) : Rel η ε L G σ τ' :=
  ⟨hk.trans hR.1, hkL.trans hR.2.1, fun f ℓ hℓ => (hlw f ℓ hℓ).trans (hR.2.2 f ℓ hℓ)⟩

variable (ι L S KLM CM) in
/-- Finsets of at most `S` elements inject into `Fin S → Option X`. -/
theorem card_small_le (X : Type) [Fintype X] [DecidableEq X] :
    Fintype.card {s : Finset X // s.card ≤ S} ≤ (Fintype.card X + 1) ^ S := by
  classical
  have hinj : Function.Injective (fun s : {s : Finset X // s.card ≤ S} => fun i : Fin S => s.1.toList[(i : ℕ)]?) := by
    intro s t h
    have hl : s.1.toList = t.1.toList := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < S
      · exact congrFun h ⟨i, hi⟩
      · have hs : s.1.toList.length ≤ i := by rw [Finset.length_toList]; have := s.2; omega
        have ht : t.1.toList.length ≤ i := by rw [Finset.length_toList]; have := t.2; omega
        rw [List.getElem?_eq_none hs, List.getElem?_eq_none ht]
    apply Subtype.ext
    rw [← Finset.toList_toFinset s.1, ← Finset.toList_toFinset t.1, hl]
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_fun, Fintype.card_option] using this

variable (ι L S KM KLM CM) in
/-- **The finite twin's state count.** -/
theorem card_FS : Fintype.card (FS ι L S KM KLM CM) ≤
    (KM + 1) * (KLM + 1) * ((Fintype.card ι + 1) * ((CM + 1) * (KLM + 1)) ^ (L + 1) + 1) ^ S := by
  classical
  have h := card_small_le S (XE ι L KLM CM)
  have hX : Fintype.card (XE ι L KLM CM) = (Fintype.card ι + 1) * ((CM + 1) * (KLM + 1)) ^ (L + 1) := by
    simp [XE, Fintype.card_prod, Fintype.card_option, Fintype.card_fun]
  rw [hX] at h
  simp only [FS, Fintype.card_prod, Fintype.card_fin]
  rw [mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by convert h))

end enc

end Pool.P0236
