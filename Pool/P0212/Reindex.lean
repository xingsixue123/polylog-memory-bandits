import Pool.Prelude

/-!
# Learner-time reindexing: sums over the flagged rounds of `[s, s')` are sums over the learner times they occupy
-/

namespace Pool.P0212

open Finset

/-- Number of flagged rounds before `u`. -/
def cntF (g : ℕ → Bool) (u : ℕ) : ℕ := ((Finset.range u).filter fun v => g v = true).card

theorem cntF_succ (g : ℕ → Bool) (u : ℕ) : cntF g (u + 1) = cntF g u + if g u = true then 1 else 0 := by
  unfold cntF
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem cntF_mono (g : ℕ → Bool) {u v : ℕ} (h : u ≤ v) : cntF g u ≤ cntF g v :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem cntF_lt_of_flag (g : ℕ → Bool) {u v : ℕ} (huv : u < v) (hg : g u = true) : cntF g u < cntF g v := by
  have h1 := cntF_succ g u
  rw [if_pos hg] at h1
  have := cntF_mono g (show u + 1 ≤ v by omega)
  omega

/-- **Reindexing.** -/
theorem sum_flag_reindex (g : ℕ → Bool) (F : ℕ → ℝ) {s : ℕ} : ∀ s', s ≤ s' →
    ∑ u ∈ Ico s s', (if g u = true then F (cntF g u) else 0) = ∑ t ∈ Ico (cntF g s) (cntF g s'), F t := by
  intro s' h
  induction s', h using Nat.le_induction with
  | base => simp
  | succ s' hs ih =>
    rw [Finset.sum_Ico_succ_top hs, ih, cntF_succ]
    split_ifs with hg
    · rw [Finset.sum_Ico_succ_top (cntF_mono g hs)]
    · simp

/-- Every learner time between `cntF s` and `cntF s'` is the learner time of a flagged round of `[s, s')`. -/
theorem exists_flag (g : ℕ → Bool) {s : ℕ} : ∀ s', s ≤ s' → ∀ t, cntF g s ≤ t → t < cntF g s' →
    ∃ u, s ≤ u ∧ u < s' ∧ g u = true ∧ cntF g u = t := by
  intro s' h
  induction s', h using Nat.le_induction with
  | base => intro t h1 h2; omega
  | succ s' hs ih =>
    intro t h1 h2
    rw [cntF_succ] at h2
    by_cases ht : t < cntF g s'
    · obtain ⟨u, hu1, hu2, hu3, hu4⟩ := ih t h1 ht
      exact ⟨u, hu1, by omega, hu3, hu4⟩
    · split_ifs at h2 with hg
      · exact ⟨s', hs, by omega, hg, by omega⟩
      · omega

end Pool.P0212
