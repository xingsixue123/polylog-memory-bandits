import Pool.P0081.Threads

/-!
# Slot count for P0065's threaded process (completes P0081)

Under the schedule `levTh` (a thread-`r` epoch `a` ends with merges of levels `0..min(ν₂(a+1), L)`, P0062's
`levPR`, where `a = (x+1)/Bt r − 1` is the GLOBAL thread-`r` epoch index; a PR23-type schedule as read here — PR23's
epoch counter may restart with each restart of the thread, and the two can differ, e.g. at the last epoch before a
restart, where `levTh` may merge more levels up to the cap), every copy has at most `D·(2L + NE/2^L + 1)` thread-merge slots
before unit `NE` (`card_slotsT_le`). With P0081's `tpools_erase_of_slots_lt`, false filter bits on these
fixed coordinates give non-interference up to `NE` (`tpools_erase_of_slotsT`).
-/

open Finset Pool.P0065 Pool.P0081

namespace Pool.P0085

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E : ι → ℕ} {thr0 : ι → ℕ} {D : ℕ} {Bt : ℕ → ℕ}

/-- A PR23-type per-thread schedule (as read here): at the end of thread-`r` epoch `a = (x+1)/Bt r - 1` (the GLOBAL
thread-`r` epoch index, not reset at restarts), merge levels `0..min(ν₂(a+1), L)`. -/
def levTh (L : ℕ) (Bt : ℕ → ℕ) (r x : ℕ) : ℕ := Pool.P0062.levPR L ((x + 1) / Bt r - 1)

theorem tl_step_same {lev : ℕ → ℕ → ℕ} {c : ι} {x : ℕ} (hE : E c ≤ x)
    (hcur : curT E thr0 D Bt c (x + 1) = curT E thr0 D Bt c x) :
    tl E thr0 D Bt lev c (x + 1) =
      if Bt (curT E thr0 D Bt c x) ∣ x + 1 then max (tl E thr0 D Bt lev c x) (lev (curT E thr0 D Bt c x) x + 1)
      else tl E thr0 D Bt lev c x := by
  rw [tl_succ_of_lt (by omega), hcur, if_neg (lt_irrefl _)]
  rfl

/-- **Level within a thread visit = P0062's one-level level in the thread's epoch index.** -/
theorem tl_eq_lvl {L : ℕ} {c : ι} {r s : ℕ} (hBr : 0 < Bt r) (hs : Bt r ∣ s) (hEs : E c ≤ s)
    (h0 : tl E thr0 D Bt (levTh L Bt) c s = 0) :
    ∀ d, (∀ y, s ≤ y → y ≤ s + d → curT E thr0 D Bt c y = r) →
      tl E thr0 D Bt (levTh L Bt) c (s + d) =
        Pool.P0062.lvl (Pool.P0062.levPR L) (s / Bt r) ((s + d) / Bt r) := by
  intro d
  induction d with
  | zero => intro _; simp [h0, Pool.P0062.lvl_self]
  | succ d ih =>
    intro hthr
    have hx := hthr (s + d) (by omega) (by omega)
    have hx1 := hthr (s + d + 1) (by omega) (by omega)
    have ih' := ih (fun y h1 h2 => hthr y h1 (by omega))
    rw [← add_assoc, tl_step_same (by omega) (by rw [hx1, hx]), hx, Nat.succ_div]
    have hle : s / Bt r ≤ (s + d) / Bt r := Nat.div_le_div_right (by omega)
    split_ifs with hdvd
    · rw [ih', Pool.P0062.lvl_succ _ _ _ hle]
      unfold levTh
      rw [Nat.succ_div, if_pos hdvd, Nat.add_sub_cancel]
    · rw [add_zero, ih']


theorem tl_entry {lev : ℕ → ℕ → ℕ} (c : ι) : tl E thr0 D Bt lev c (E c) = 0 := by
  rcases Nat.eq_zero_or_pos (E c) with h | h
  · rw [h]; rfl
  · obtain ⟨k, hk⟩ : ∃ k, E c = k + 1 := ⟨E c - 1, by omega⟩
    rw [hk]; simp [tl, ← hk]

/-- **Visit start.** The first unit `s ∈ [E c, NE)` at which `c`'s current thread is `r` is a multiple of `Bt r`
with level `0`, and `c` stays in thread `r` from `s` to any later unit where it is in thread `r`. -/
theorem visit_start {L : ℕ} (hB : BtHyp D Bt) {c : ι} (hent : Bt (thr0 c) ∣ E c) (hthr : thr0 c < D) {r NE : ℕ}
    (hex : ∃ x, E c ≤ x ∧ x < NE ∧ curT E thr0 D Bt c x = r) :
    ∃ s, E c ≤ s ∧ Bt r ∣ s ∧ tl E thr0 D Bt (levTh L Bt) c s = 0 ∧
      ∀ x, E c ≤ x → x < NE → curT E thr0 D Bt c x = r → s ≤ x ∧
        ∀ y, s ≤ y → y ≤ x → curT E thr0 D Bt c y = r := by
  classical
  let P : ℕ → Prop := fun x => E c ≤ x ∧ x < NE ∧ curT E thr0 D Bt c x = r
  have hP : ∃ x, P x := hex
  have hspec0 := Nat.find_spec hP
  have hmin0 : ∀ x, P x → Nat.find hP ≤ x := fun x hx => Nat.find_min' hP hx
  generalize Nat.find hP = s at hspec0 hmin0
  obtain ⟨hEs, hsN, hsr⟩ := hspec0
  have hmin := hmin0
  have hrD : r < D := hsr ▸ lt_of_le_of_lt (curT_le_thr0 c s) hthr
  have hstay : ∀ x, P x → ∀ y, s ≤ y → y ≤ x → curT E thr0 D Bt c y = r := by
    intro x hx y h1 h2
    have a1 := curT_mono (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c h2 (by omega)
    have a2 := curT_mono (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c h1 hEs
    rw [hx.2.2] at a1; rw [hsr] at a2; omega
  rcases eq_or_lt_of_le hEs with heq | hlt
  · refine ⟨s, hEs, ?_, ?_, fun x h1 h2 h3 => ⟨hmin x ⟨h1, h2, h3⟩, hstay x ⟨h1, h2, h3⟩⟩⟩
    · rw [← hsr, ← heq, curT_of_le le_rfl]; exact hent
    · rw [← heq]; exact tl_entry c
  · obtain ⟨s', hs'⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hprev : curT E thr0 D Bt c s' ≠ r := by
      intro h; have := hmin s' ⟨by omega, by omega, h⟩; omega
    have hmono := curT_mono (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c (show s' ≤ s' + 1 by omega) (by omega)
    rw [← hs', hsr] at hmono
    have hlt' : r < curT E thr0 D Bt c s' := lt_of_le_of_ne hmono (Ne.symm hprev)
    have hcan : canonT D Bt s = r := by
      have := curT_succ (E := E) (thr0 := thr0) (D := D) (Bt := Bt) (c := c) (x := s') (by omega)
      rw [← hs', hsr] at this
      rcases min_choice (curT E thr0 D Bt c s') (canonT D Bt s) with h | h
      · rw [h] at this; omega
      · rw [h] at this; exact this.symm
    refine ⟨s, hEs, ?_, ?_, fun x h1 h2 h3 => ⟨hmin x ⟨h1, h2, h3⟩, hstay x ⟨h1, h2, h3⟩⟩⟩
    · have hspec := Nat.find_spec (⟨D - 1, Or.inr le_rfl⟩ : ∃ j, Bt j ∣ s ∨ D - 1 ≤ j)
      have : canonT D Bt s = Nat.find (⟨D - 1, Or.inr le_rfl⟩ : ∃ j, Bt j ∣ s ∨ D - 1 ≤ j) := rfl
      rw [← this, hcan] at hspec
      rcases hspec with h | h
      · exact h
      · have : r = D - 1 := by omega
        rw [this, hB.last]; exact one_dvd _
    · rw [hs', tl_succ_of_lt (by omega), if_pos (by rw [← hs', hsr]; exact hlt')]


variable (E thr0 D Bt) in
/-- The thread-merge slots `(x, ℓ)`, `x < NE`, of copy `c` under the schedule `levTh L Bt`. -/
noncomputable def slotsT (L NE : ℕ) (c : ι) : Finset (ℕ × ℕ) := by
  classical
  exact ((Ico (E c) NE) ×ˢ (range (L + 1))).filter
    (fun p => InSlotsT E thr0 D Bt (levTh L Bt) c p.1 p.2)

theorem mem_slotsT {L NE x ℓ : ℕ} {c : ι} (hx : x < NE) (h : InSlotsT E thr0 D Bt (levTh L Bt) c x ℓ) :
    (x, ℓ) ∈ slotsT E thr0 D Bt L NE c := by
  classical
  unfold slotsT
  simp only [mem_filter, mem_product, mem_Ico, mem_range]
  refine ⟨⟨⟨h.1, hx⟩, ?_⟩, h⟩
  have := h.2.2.1
  have := Pool.P0062.levPR_le L ((x + 1) / Bt (curT E thr0 D Bt c x) - 1)
  unfold levTh at *
  omega

/-- **Thread slot count.** Under the schedule `levTh` (global thread-epoch index), a copy takes part in at most `D (2L + NE/2^L + 1)`
merges before unit `NE`: at most `D` thread visits, each a run of P0062's one-level dynamics. -/
theorem card_slotsT_le {L NE : ℕ} (hB : BtHyp D Bt) {c : ι} (hent : Bt (thr0 c) ∣ E c) (hthr : thr0 c < D) :
    (slotsT E thr0 D Bt L NE c).card ≤ D * (2 * L + NE / 2 ^ L + 1) := by
  classical
  have hsub : slotsT E thr0 D Bt L NE c ⊆ (range D).biUnion
      (fun r => (slotsT E thr0 D Bt L NE c).filter (fun p => curT E thr0 D Bt c p.1 = r)) := by
    intro p hp
    simp only [mem_biUnion, mem_range, mem_filter]
    exact ⟨curT E thr0 D Bt c p.1, lt_of_le_of_lt (curT_le_thr0 c p.1) hthr, hp, rfl⟩
  have hr : ∀ r ∈ range D, ((slotsT E thr0 D Bt L NE c).filter (fun p => curT E thr0 D Bt c p.1 = r)).card ≤
      2 * L + NE / 2 ^ L + 1 := by
    intro r _
    set X := (slotsT E thr0 D Bt L NE c).filter (fun p => curT E thr0 D Bt c p.1 = r)
    by_cases hne : X.Nonempty
    · obtain ⟨⟨x0, ℓ0⟩, hx0⟩ := hne
      simp only [X, slotsT, mem_filter, mem_product, mem_Ico, mem_range] at hx0
      obtain ⟨s, hEs, hsd, hs0, hvis⟩ := visit_start (L := L) hB hent hthr ⟨x0, hx0.1.1.1.1, hx0.1.1.1.2, hx0.2⟩
      have hBr := hB.pos r
      have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 / Bt r, p.2)) X := by
        rintro ⟨x1, ℓ1⟩ h1 ⟨x2, ℓ2⟩ h2 heq
        simp only [X, slotsT, coe_filter, mem_filter, mem_product, mem_Ico, mem_range, Set.mem_ofPred_eq] at h1 h2
        simp only [Prod.mk.injEq] at heq ⊢
        refine ⟨?_, heq.2⟩
        have d1 := h1.1.2.2.1; rw [h1.2] at d1
        have d2 := h2.1.2.2.1; rw [h2.2] at d2
        have e1 := Nat.succ_div (a := x1) (b := Bt r); rw [if_pos d1] at e1
        have e2 := Nat.succ_div (a := x2) (b := Bt r); rw [if_pos d2] at e2
        have m1 := Nat.div_mul_cancel d1
        have m2 := Nat.div_mul_cancel d2
        rw [e1, heq.1, ← e2] at m1
        omega
      calc X.card ≤ (Pool.P0062.slots L (s / Bt r) NE).card := by
            apply card_le_card_of_injOn _ (fun p hp => ?_) hinj
            obtain ⟨x, ℓ⟩ := p
            simp only [X, slotsT, coe_filter, mem_filter, mem_product, mem_Ico, mem_range, Set.mem_ofPred_eq] at hp
            obtain ⟨⟨⟨⟨hxE, hxN⟩, -⟩, hsl⟩, hcur⟩ := hp
            obtain ⟨hsx, hstay⟩ := hvis x hxE hxN hcur
            have hd : Bt r ∣ x + 1 := by have := hsl.2.1; rwa [hcur] at this
            have hsucc : (x + 1) / Bt r - 1 = x / Bt r := by
              rw [Nat.succ_div (a := x) (b := Bt r), if_pos hd, Nat.add_sub_cancel]
            have htl := tl_eq_lvl (L := L) hBr hsd hEs hs0 (x - s) (fun y h1 h2 => hstay y h1 (by omega))
            rw [show s + (x - s) = x by omega] at htl
            simp only [coe_product, mem_coe]
            apply Pool.P0062.mem_slots (lt_of_le_of_lt (Nat.div_le_self x (Bt r)) hxN)
            refine ⟨Nat.div_le_div_right hsx, ?_, ?_⟩
            · have := hsl.2.2.1; rw [hcur] at this; unfold levTh at this; rwa [hsucc] at this
            · have := hsl.2.2.2; rwa [htl] at this
        _ ≤ 2 * L + NE / 2 ^ L + 1 := Pool.P0062.card_slots_le L _ NE
    · rw [Finset.not_nonempty_iff_eq_empty] at hne; rw [hne]; simp
  calc (slotsT E thr0 D Bt L NE c).card ≤ _ := card_le_card hsub
    _ ≤ ∑ r ∈ range D, ((slotsT E thr0 D Bt L NE c).filter (fun p => curT E thr0 D Bt c p.1 = r)).card :=
        card_biUnion_le
    _ ≤ ∑ r ∈ range D, (2 * L + NE / 2 ^ L + 1) := sum_le_sum hr
    _ = D * (2 * L + NE / 2 ^ L + 1) := by simp

/-- **Non-interference from the counted slots.** If copy `c`'s filter bits are false on the fixed coordinates
`slotsT L NE c` (at most `D (2L + NE/2^L + 1)` of them per filter index `k`), removing `c` does not change the
threaded pools up to unit `NE`. -/
theorem tpools_erase_of_slotsT {C : ι → ℕ → ℝ} {θ : ℝ} {R K Lv L NE : ℕ} (c : ι) (ωs ωs' : ι → Bool)
    (hs : Pool.P0052.AgreeOff c ωs ωs') (hs' : ωs' c = false) (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (hφ : ∀ p ∈ slotsT E thr0 D Bt L NE c, ∀ k, φ (curT E thr0 D Bt c p.1) p.1 p.2 k c = false)
    (hφ' : ∀ r a ℓ k, Pool.P0052.AgreeOff c (φ r a ℓ k) (φ' r a ℓ k)) :
    ∀ a, a ≤ NE → ∀ r ℓ, (tpools E thr0 C θ R K D Lv Bt (levTh L Bt) ωs φ a r ℓ).erase c =
      tpools E thr0 C θ R K D Lv Bt (levTh L Bt) ωs' φ' a r ℓ :=
  tpools_erase_of_slots_lt NE c ωs ωs' hs hs' φ φ' (fun x ℓ k hx h => hφ (x, ℓ) (mem_slotsT hx h) k) hφ'

end Pool.P0085
