import Pool.P0236.Machine

/-!
# On fitting runs, the finite twin plays exactly as the self-rounding ALG
-/

namespace Pool.P0236

open Pool.P0230 Real Finset Pool.P0089 Pool.P0102 Pool.P0212 Pool.P0194 Pool.P0001

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι]
  (P : ParD n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ)

/-- The self-rounding ALG's parameters. -/
noncomputable abbrev PG : ParD n ι := Pool.P0225.withAlgG P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε)

variable (ℓ : LossSeq n) (ω : ℕ → RC (PG P η ε L N G γ wE)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (PG P η ε L N G γ wE).K → ι → Bool)

theorem kE_le (u : ℕ) : Pool.P0225.kE P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ω u ≤ u := by
  unfold Pool.P0225.kE; exact (Finset.card_filter_le _ _).trans (by simp)

/-- The presence recorded at learner time `v` is the active set of the exploitation round of that learner time. -/
theorem pr_written (u v : ℕ) (hv : v < (sA (PG P η ε L N G γ wE) ℓ ω ωs φ u).k) :
    ∃ e < u, isE (PG P η ε L N G γ wE) (ω e).1 = true ∧
      (sA (PG P η ε L N G γ wE) ℓ ω ωs φ e).k = v ∧
      (sA (PG P η ε L N G γ wE) ℓ ω ωs φ u).pr v = presOf (active (PG P η ε L N G γ wE) ℓ ω ωs φ e) := by
  rw [Pool.P0225.sA_k] at hv
  obtain ⟨e, -, he, hg, hcnt⟩ := exists_flag (Pool.P0225.gE P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ω)
    u (Nat.zero_le u) v (Nat.zero_le _) hv
  have hke : (sA (PG P η ε L N G γ wE) ℓ ω ωs φ e).k = v := by rw [Pool.P0225.sA_k]; exact hcnt
  have hw := Pool.P0225.sA_written P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ω ωs φ hg
  have hfz := (Pool.P0225.sA_frozen P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ω ωs φ (e + 1) u he
    (sA (PG P η ε L N G γ wE) ℓ ω ωs φ e).k (by rw [hw.1]; exact Nat.lt_succ_self _)).2.1
  refine ⟨e, he, hg, hke, ?_⟩
  rw [← hke]
  exact hfz.trans hw.2.2.1

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
include hD hLv hlev

/-- **New active copies were never present before** (from P0215's activity intervals). -/
theorem hentV_run (u : ℕ) :
    HentV (sA (PG P η ε L N G γ wE) ℓ ω ωs φ u) (active (PG P η ε L N G γ wE) ℓ ω ωs φ u) := by
  intro v hv f hf hfv v' hv' hfv'
  obtain ⟨e, he, hge, hke, hpe⟩ := pr_written P η ε L N G γ wE ℓ ω ωs φ u v (by omega)
  obtain ⟨e', he', hge', hke', hpe'⟩ := pr_written P η ε L N G γ wE ℓ ω ωs φ u v' (by omega)
  have hfv0 : (sA (PG P η ε L N G γ wE) ℓ ω ωs φ u).pr v f ≠ true := by simpa [prH] using hfv
  have hfv0' : (sA (PG P η ε L N G γ wE) ℓ ω ωs φ u).pr v' f = true := by simpa [prH] using hfv'
  rw [hpe] at hfv0
  rw [hpe'] at hfv0'
  cases f with
  | none => exact hfv0 rfl
  | some x =>
    have hxu : x ∈ active (PG P η ε L N G γ wE) ℓ ω ωs φ u := by
      rw [mem_Pk] at hf; simpa [presOf] using hf
    have hxe' : x ∈ active (PG P η ε L N G γ wE) ℓ ω ωs φ e' := by simpa [presOf] using hfv0'
    have hxe : x ∉ active (PG P η ε L N G γ wE) ℓ ω ωs φ e := by simpa [presOf] using hfv0
    -- `e' ≤ e`: learner times are increasing along exploitation rounds
    have hee : e' ≤ e := by
      by_contra hlt
      push Not at hlt
      have h1 : Pool.P0225.kE P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ω e <
          Pool.P0225.kE P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ω e' :=
        cntF_lt_of_flag (Pool.P0225.gE P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ω) hlt hge
      have hk1 := hke; rw [Pool.P0225.sA_k] at hk1
      have hk2 := hke'; rw [Pool.P0225.sA_k] at hk2
      omega
    obtain ⟨b, hEb, -, hiff⟩ := Pool.P0215.active_interval (PG P η ε L N G γ wE) ℓ ω ωs φ hD hLv hlev (u + 1) x
      ⟨u, Nat.lt_succ_self u, hxu⟩
    have h1 := (hiff e' (by omega)).1 hxe'
    have h2 := (hiff u (Nat.lt_succ_self u)).1 hxu
    exact hxe ((hiff e (by omega)).2 ⟨by omega, by omega⟩)

variable {S KM : ℕ} (hG : 0 < G) (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η) (T : ℕ)
  (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM) (hfit : ∀ u < T, (active (PG P η ε L N G γ wE) ℓ ω ωs φ u).card + 1 ≤ S)
include hG hγ hwE hε hη hTL hTK hfit

theorem good_run : ∀ u < T, GoodF (L := L) (S := S) (KM := KM) (sA (PG P η ε L N G γ wE) ℓ ω ωs φ u)
    (active (PG P η ε L N G γ wE) ℓ ω ωs φ u) := by
  intro u hu
  have hk : (sA (PG P η ε L N G γ wE) ℓ ω ωs φ u).k ≤ u := by
    rw [Pool.P0225.sA_k]; exact kE_le P η ε L N G γ wE ω u
  exact ⟨hentV_run P η ε L N G γ wE ℓ ω ωs φ hD hLv hlev u, by omega, hfit u hu, by omega⟩

/-- **On fitting runs, the finite twin's ALG choices are the self-rounding ALG's** before `T`. -/
theorem algCh_twin {u : ℕ} (hu : u < T) :
    algCh (withTwin P η ε L N G γ wE S KM) ℓ ω ωs φ u = algCh (PG P η ε L N G γ wE) ℓ ω ωs φ u :=
  algCh_sim ℓ ω ωs φ (RelF (η := η) (ε := ε) (L := L) (G := G) (γ := γ) (wE := wE) (S := S) (KM := KM))
    (GoodF (L := L) (S := S) (KM := KM)) (relF_start hε hη)
    (fun σ τ V d hR hg => draw_sim (N := N) hG hR hg d)
    (fun σ τ V d ch bit hR hg => upd_sim (N := N) hG hγ hwE hε hη hR hg d ch bit) T
    (good_run P η ε L N G γ wE ℓ ω ωs φ hD hLv hlev hG hγ hwE hε hη T hTL hTK hfit) hu

/-- **On fitting runs, the finite twin's plays are the self-rounding ALG's** before `T`. -/
theorem play_twin {u : ℕ} (hu : u < T) :
    play (withTwin P η ε L N G γ wE S KM) ℓ ω ωs φ u = play (PG P η ε L N G γ wE) ℓ ω ωs φ u :=
  play_sim ℓ ω ωs φ (RelF (η := η) (ε := ε) (L := L) (G := G) (γ := γ) (wE := wE) (S := S) (KM := KM))
    (GoodF (L := L) (S := S) (KM := KM)) (relF_start hε hη)
    (fun σ τ V d hR hg => draw_sim (N := N) hG hR hg d)
    (fun σ τ V d ch bit hR hg => upd_sim (N := N) hG hγ hwE hε hη hR hg d ch bit) T
    (good_run P η ε L N G γ wE ℓ ω ωs φ hD hLv hlev hG hγ hwE hε hη T hTL hTK hfit) hu

/-- **On fitting runs, the finite twin's policy losses are the self-rounding ALG's** before `T`. -/
theorem aPol_twin {u : ℕ} (hu : u < T) :
    aPol (withTwin P η ε L N G γ wE S KM) ℓ ωs φ ω u = aPol (PG P η ε L N G γ wE) ℓ ωs φ ω u :=
  aPol_sim ℓ ω ωs φ (RelF (η := η) (ε := ε) (L := L) (G := G) (γ := γ) (wE := wE) (S := S) (KM := KM))
    (GoodF (L := L) (S := S) (KM := KM)) (relF_start hε hη)
    (fun σ τ V d hR hg => draw_sim (N := N) hG hR hg d)
    (fun σ τ V d ch bit hR hg => upd_sim (N := N) hG hγ hwE hε hη hR hg d ch bit) T
    (good_run P η ε L N G γ wE ℓ ω ωs φ hD hLv hlev hG hγ hwE hε hη T hTL hTK hfit) hu

end Pool.P0236
