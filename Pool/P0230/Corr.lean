import Pool.P0230.Twin

/-!
# The abstract twin computes the self-rounding ALG's marginal, and the correspondence is preserved
-/

namespace Pool.P0230

open Real Finset Pool.P0019 Pool.P0089 Pool.P0102 Pool.P0212

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ)

/-- Presence sets of an ALG state at its learner times. -/
def prH (σ : AState ι) (t : ℕ) : Finset (Option ι) := univ.filter fun f => σ.pr t f = true

/-- Presence sets with the current active set at the current learner time. -/
def prX (σ : AState ι) (V : Finset ι) (t : ℕ) : Finset (Option ι) := if t < σ.k then prH σ t else Pk V

/-- Integer IX losses read from an ALG state. -/
noncomputable def bH (σ : AState ι) (t : ℕ) (f : Option ι) : ℕ := ⌊(G : ℝ) * σ.c t f⌋₊

/-- Invariants of the self-rounding ALG's state: grid data, self-rounding perturbations, copies never come back. -/
structure Inv (σ : AState ι) : Prop where
  grid : ∀ t < σ.k, ∀ f, σ.c t f = (bH G σ t f : ℝ) / G
  self : ∀ t < σ.k, σ.ρ t = Pool.P0225.selfRho ε
    (pw (fun _ => (1 : ℝ)) η (aw L (prH σ)) (specLoss (L := L) (cR (bH G σ) G)) σ.ρ t)
    (aw L (prH σ) t) η (specLoss (L := L) (cR (bH G σ) G) t)
  ent : ∀ u, u + 1 < σ.k → ∀ f ∈ prH σ (u + 1), f ∉ prH σ u → ∀ u' ≤ u, f ∉ prH σ u'

/-- The new experts of `V` at the current learner time were never present before. -/
def HentV (σ : AState ι) (V : Finset ι) : Prop :=
  ∀ u, u + 1 = σ.k → ∀ f ∈ Pk V, f ∉ prH σ u → ∀ u' ≤ u, f ∉ prH σ u'

/-- The twin represents the ALG state: same learner time, and P0102's run of the state's data. -/
def Rel (σ : AState ι) (τ : TS ι) : Prop :=
  τ.k = σ.k ∧ τ.kL = kLr L (prH σ) (bH G σ) G η ε σ.k ∧
    ∀ f, ∀ ℓ ≤ L, lwOf τ f ℓ = lwr L (prH σ) (bH G σ) G η ε σ.k f ℓ

variable {η ε L G}

theorem prX_lt {σ : AState ι} {V : Finset ι} {t : ℕ} (ht : t < σ.k) : prX σ V t = prH σ t := if_pos ht

theorem prX_k (σ : AState ι) (V : Finset ι) : prX σ V σ.k = Pk V := if_neg (lt_irrefl _)

theorem hent_prX {σ : AState ι} {V : Finset ι} (hI : Inv η ε L G σ) (hV : HentV σ V) :
    ∀ u, ∀ f ∈ prX σ V (u + 1), f ∉ prX σ V u → ∀ u' ≤ u, f ∉ prX σ V u' := by
  intro u f hf hfu u' hu'
  rcases lt_trichotomy (u + 1) σ.k with h | h | h
  · rw [prX_lt h] at hf; rw [prX_lt (by omega)] at hfu ⊢
    exact hI.ent u h f hf hfu u' hu'
  · rw [h, prX_k] at hf; rw [prX_lt (by omega)] at hfu ⊢
    exact hV u h f hf hfu u' hu'
  · exfalso
    rw [prX, if_neg (by omega)] at hf hfu
    exact hfu hf

/-- `aw` for the extended presence agrees with the state's at learner times `< k`. -/
theorem aw_prX_lt {σ : AState ι} {V : Finset ι} {t : ℕ} (ht : t < σ.k) : aw L (prX σ V) t = aw L (prH σ) t := by
  funext s; simp only [aw, specAw, decide_eq_decide, prX_lt ht]

theorem cR_bH_lt {σ : AState ι} (hI : Inv η ε L G σ) {t : ℕ} (ht : t < σ.k) :
    specLoss (L := L) (cR (bH G σ) G) t = specLoss (L := L) σ.c t := by
  funext s; simp only [specLoss, cR]; exact (hI.grid t ht s.1).symm

/-- The self-rounding hypothesis of `selfRound_pw` for the extended presence. -/
theorem self_prX {σ : AState ι} {V : Finset ι} (hI : Inv η ε L G σ) :
    ∀ t < σ.k, σ.ρ t = Pool.P0225.selfRho ε
      (pw (fun _ => (1 : ℝ)) η (aw L (prX σ V)) (specLoss (L := L) (cR (bH G σ) G)) σ.ρ t)
      (aw L (prX σ V) t) η (specLoss (L := L) (cR (bH G σ) G) t) := by
  intro t ht
  rw [hI.self t ht, aw_prX_lt ht, Pool.P0134.pw_congr _ _ t fun s hs => ⟨aw_prX_lt (by omega), rfl, rfl⟩]

/-- **The twin's marginal is the ALG's marginal.** -/
theorem pmargT_eq (hG : 0 < G) {σ : AState ι} {τ : TS ι} {V : Finset ι} (hI : Inv η ε L G σ)
    (hR : Rel η ε L G σ τ) (hV : HentV σ V) (hk : σ.k < 2 ^ L) :
    pmargT η ε L G τ V = pmarg η L σ V := by
  have hent := hent_prX hI hV
  have hρ := self_prX (V := V) hI
  have hK : σ.k ≤ 2 ^ L := hk.le
  -- P0089's awake indicator and losses of `pmarg`, rewritten
  have hpres : ∀ t f, prAt σ V t f ↔ f ∈ prX σ V t := by
    intro t f
    simp only [prAt, prX, prH]
    split_ifs <;> simp [mem_Pk]
  have haw : specAw (L := L) (prAt σ V) = aw L (prX σ V) := by
    funext t s
    simp only [aw, specAw, decide_eq_decide, hpres]
  have hpp : ∀ s, pprob (fun _ => (1 : ℝ)) η (specAw (L := L) (prAt σ V)) (specLoss (L := L) σ.c) σ.ρ σ.k s =
      pprob (fun _ => (1 : ℝ)) η (aw L (prX σ V)) (specLoss (L := L) (cR (bH G σ) G)) σ.ρ σ.k s := by
    intro s
    rw [haw]
    exact congrFun (Pool.P0134.pprob_congr _ η σ.k (fun t ht => ⟨rfl, (cR_bH_lt hI ht).symm, rfl⟩) rfl) s
  have hmA := selfRound_awakeMass hG hent σ.ρ σ.k hK hρ σ.k le_rfl hk
  have hpw := selfRound_pw hG hent σ.ρ σ.k hK hρ σ.k le_rfl hk
  have hmw : ∀ f (ℓ : Fin (L + 1)), mw (η / G) ε (kLr L (prX σ V) (bH G σ) G η ε) (lwr L (prX σ V) (bH G σ) G η ε)
      σ.k f ℓ = mwT η ε G τ f ℓ := by
    intro f ℓ
    have hst : stS L (prX σ V) (bH G σ) (η / G) ε σ.k = stS L (prH σ) (bH G σ) (η / G) ε σ.k :=
      stS_congr (L := L) (η / G) ε σ.k fun s hs => ⟨prX_lt hs, rfl⟩
    unfold mw mwT kLr lwr
    rw [hst, hR.2.2 f ℓ (Nat.lt_succ_iff.1 ℓ.2), hR.2.1]
  have hmass : mA L (prX σ V) (η / G) ε (kLr L (prX σ V) (bH G σ) G η ε) (lwr L (prX σ V) (bH G σ) G η ε) σ.k =
      mAT η ε L G τ V := by
    unfold mA mAT; rw [prX_k]
    exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun ℓ _ => hmw f ℓ
  funext f
  unfold pmarg pmargT
  simp_rw [hpp]
  -- the marginal as a sum over present copies and levels
  have hsum : ∑ s ∈ univ.filter (fun s : Spec (Option ι) L => s.1 = f),
      pprob (fun _ => (1 : ℝ)) η (aw L (prX σ V)) (specLoss (L := L) (cR (bH G σ) G)) σ.ρ σ.k s =
      ∑ g ∈ prX σ V σ.k, ∑ ℓ : Fin (L + 1), if g = f then mwT η ε G τ g ℓ / mAT η ε L G τ V else 0 := by
    rw [Finset.sum_filter]
    have : ∀ s : Spec (Option ι) L, (if s.1 = f then
        pprob (fun _ => (1 : ℝ)) η (aw L (prX σ V)) (specLoss (L := L) (cR (bH G σ) G)) σ.ρ σ.k s else 0) =
        if aw L (prX σ V) σ.k s then (if s.1 = f then
          pw (fun _ => (1 : ℝ)) η (aw L (prX σ V)) (specLoss (L := L) (cR (bH G σ) G)) σ.ρ σ.k s /
            mAT η ε L G τ V else 0) else 0 := by
      intro s
      unfold pprob
      rw [hmA, hmass]
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl fun s _ => this s, sum_awake hk]
    refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases hgf : g = f
    · subst hgf
      rw [if_pos (show (spc hk g ℓ).1 = g from rfl), if_pos rfl, ← hmw]
      exact congrArg (· / mAT η ε L G τ V) (hpw g hg ℓ)
    · rw [if_neg (show (spc hk g ℓ).1 ≠ f from hgf), if_neg hgf]
  rw [hsum, prX_k]
  split_ifs with hf
  · rw [Finset.sum_eq_single f (fun g _ hgf => by simp [hgf]) (fun h => absurd hf h)]
    simp only [if_true]
    rw [Finset.sum_div]
  · exact (Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun ℓ _ => by
      rw [if_neg]; rintro rfl; exact hf hg).symm

end Pool.P0230

namespace Pool.P0230

open Real Finset Pool.P0019 Pool.P0089 Pool.P0102 Pool.P0212

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {η ε : ℝ} {L N G : ℕ} {γ wE : ℝ}

/-- The twin's integer IX losses are the ALG's, scaled by `G`. -/
theorem ixA_eq_bT (hG : 0 < G) {σ : AState ι} {τ : TS ι} {V : Finset ι} (hI : Inv η ε L G σ)
    (hR : Rel η ε L G σ τ) (hV : HentV σ V) (hk : σ.k < 2 ^ L) (ch : Option ι) (bit : Bool) (f : Option ι) :
    ixA η L N G γ wE σ V ch bit f = (bT η ε L N G γ wE τ V ch bit f : ℝ) / G := by
  rw [ixA_eq_bOfP, bT, pmargT_eq hG hI hR hV hk]

theorem floor_mul_div (hG : 0 < G) (m : ℕ) : ⌊(G : ℝ) * ((m : ℝ) / G)⌋₊ = m := by
  have : (G : ℝ) * ((m : ℝ) / G) = m := by
    have : (G : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
    field_simp
  rw [this, Nat.floor_natCast]

/-- The initial states: the invariants hold and the twin represents the ALG. -/
theorem inv_s0A : Inv η ε L G (s0A : AState ι) where
  grid t ht := absurd ht (Nat.not_lt_zero t)
  self t ht := absurd ht (Nat.not_lt_zero t)
  ent u hu := absurd hu (by simp [s0A])

theorem rel_s0A : Rel η ε L G (s0A : AState ι) (t0 : TS ι) :=
  ⟨rfl, rfl, fun f ℓ _ => by simp [lwOf, t0, s0A, lwr, stS]⟩

/-- The twin draws what the ALG draws. -/
theorem drawOf_pmargT (hG : 0 < G) {σ : AState ι} {τ : TS ι} {V : Finset ι} (hI : Inv η ε L G σ)
    (hR : Rel η ε L G σ τ) (hV : HentV σ V) (hk : σ.k < 2 ^ L) (d : Fin N) :
    drawOf N (pmargT η ε L G τ V) d = drawA η L N σ V d := by
  rw [drawA_eq_drawOf, pmargT_eq hG hI hR hV hk]

section step

variable {σ : AState ι} {τ : TS ι} {V : Finset ι} {d : Fin N} {ch : Option ι} {bit : Bool}

/-- The ALG's state after an exploitation round, with the self-rounding rule. -/
local notation "σ'" => Pool.P0225.updAG η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) σ V d ch bit

theorem prH_upd_lt {t : ℕ} (ht : t < σ.k) : prH σ' t = prH σ t := by
  simp only [prH, Pool.P0225.updAG, Function.update_of_ne ht.ne]

theorem prH_upd_k : prH σ' σ.k = Pk V := by
  ext f; simp [prH, Pool.P0225.updAG, mem_Pk]

theorem bH_upd_lt {t : ℕ} (ht : t < σ.k) : bH G σ' t = bH G σ t := by
  funext f; simp only [bH, Pool.P0225.updAG, Function.update_of_ne ht.ne]

theorem bH_upd_k (hG : 0 < G) (hI : Inv η ε L G σ) (hR : Rel η ε L G σ τ) (hV : HentV σ V) (hk : σ.k < 2 ^ L) : bH G σ' σ.k = bT η ε L N G γ wE τ V ch bit := by
  funext f
  simp only [bH, Pool.P0225.updAG, Function.update_self]
  rw [ixA_eq_bT hG hI hR hV hk, floor_mul_div hG]

theorem c_upd_k (hG : 0 < G) (hI : Inv η ε L G σ) (hR : Rel η ε L G σ τ) (hV : HentV σ V) (hk : σ.k < 2 ^ L) (f : Option ι) : (σ').c σ.k f = (bH G σ' σ.k f : ℝ) / G := by
  rw [bH_upd_k hG hI hR hV hk]
  simp only [Pool.P0225.updAG, Function.update_self]
  exact ixA_eq_bT hG hI hR hV hk ch bit f

/-- **Exploitation rounds preserve the invariants.** -/
theorem inv_upd (hG : 0 < G) (hI : Inv η ε L G σ) (hR : Rel η ε L G σ τ) (hV : HentV σ V) (hk : σ.k < 2 ^ L) : Inv η ε L G σ' := by
  have hk' : (σ').k = σ.k + 1 := rfl
  -- agreement of the data below `σ.k`
  have hagr : ∀ s < σ.k, aw L (prH σ') s = aw L (prH σ) s ∧
      specLoss (L := L) (cR (bH G σ') G) s = specLoss (L := L) (cR (bH G σ) G) s ∧ (σ').ρ s = σ.ρ s := by
    intro s hs
    refine ⟨?_, ?_, ?_⟩
    · funext x; simp only [aw, specAw, decide_eq_decide, prH_upd_lt hs]
    · funext x; simp only [specLoss, cR, bH_upd_lt hs]
    · simp only [Pool.P0225.updAG, Function.update_of_ne hs.ne]
  -- the grid invariant
  have hgrid : ∀ t < (σ').k, ∀ f, (σ').c t f = (bH G σ' t f : ℝ) / G := by
    intro t ht f
    rcases Nat.lt_or_ge t σ.k with h | h
    · have : (σ').c t f = σ.c t f := by simp only [Pool.P0225.updAG, Function.update_of_ne h.ne]
      rw [this, hI.grid t h f, bH_upd_lt h]
    · have : t = σ.k := by omega
      subst this; exact c_upd_k hG hI hR hV hk f
  refine ⟨hgrid, ?_, ?_⟩
  · intro t ht
    rcases Nat.lt_or_ge t σ.k with h | h
    · have hρt : (σ').ρ t = σ.ρ t := (hagr t h).2.2
      rw [hρt, hI.self t h, Pool.P0134.pw_congr _ _ t fun s hs => ⟨((hagr s (by omega)).1).symm, ((hagr s (by omega)).2.1).symm, ((hagr s (by omega)).2.2).symm⟩,
        (hagr t h).1, (hagr t h).2.1]
    · have : t = σ.k := by omega
      subst this
      have hρk : (σ').ρ σ.k = Pool.P0225.ρStar η L N G γ wE ε σ V ch bit := by
        simp only [Pool.P0225.updAG, Function.update_self]
      -- the rule's awake indicator and data are the updated state's, up to learner time `σ.k`
      have haw : ∀ s ≤ σ.k, Pool.P0225.awS L σ V s = aw L (prH σ') s := by
        intro s hs
        funext x
        simp only [Pool.P0225.awS, aw, specAw, decide_eq_decide]
        rcases Nat.lt_or_ge s σ.k with h' | h'
        · have hp : (σ').pr s = σ.pr s := by simp only [Pool.P0225.updAG, Function.update_of_ne h'.ne]
          simp [prAt, h', prH, hp]
        · have : s = σ.k := by omega
          subst this
          simp [prAt, prH_upd_k, mem_Pk]
      have hcc : ∀ s ≤ σ.k, Pool.P0225.ccS η L N G γ wE σ V ch bit s =
          specLoss (L := L) (cR (bH G σ') G) s := by
        intro s hs
        funext x
        simp only [Pool.P0225.ccS, specLoss, cR]
        exact hgrid s (by rw [hk']; omega) x.1
      rw [hρk, show Pool.P0225.ρStar η L N G γ wE ε σ V ch bit = Pool.P0225.selfRho ε
          (pw (fun _ => (1 : ℝ)) η (Pool.P0225.awS L σ V) (Pool.P0225.ccS η L N G γ wE σ V ch bit) σ.ρ σ.k)
          (Pool.P0225.awS L σ V σ.k) η (Pool.P0225.ccS η L N G γ wE σ V ch bit σ.k) from rfl]
      rw [haw σ.k le_rfl, hcc σ.k le_rfl,
        Pool.P0134.pw_congr _ _ σ.k fun s hs => ⟨haw s hs.le, hcc s hs.le, (hagr s hs).2.2.symm⟩]
  · intro u hu f hf hfu u' hu'
    rcases Nat.lt_or_ge (u + 1) σ.k with h | h
    · rw [prH_upd_lt h] at hf
      rw [prH_upd_lt (by omega)] at hfu ⊢
      exact hI.ent u h f hf hfu u' hu'
    · have h' : u + 1 = σ.k := by omega
      rw [h', prH_upd_k] at hf
      rw [prH_upd_lt (by omega)] at hfu ⊢
      exact hV u h' f hf hfu u' hu'

/-- **Exploitation rounds preserve the twin relation.** -/
theorem rel_upd (hG : 0 < G) (hI : Inv η ε L G σ) (hR : Rel η ε L G σ τ) (hV : HentV σ V) (hk : σ.k < 2 ^ L) :
    Rel η ε L G σ' (updT η ε L N G γ wE τ V ch bit) := by
  set S := stS L (prH σ) (bH G σ) (η / G) ε σ.k with hS
  have hS' : stS L (prH σ') (bH G σ') (η / G) ε σ.k = S :=
    stS_congr (L := L) (η / G) ε σ.k fun s hs => ⟨prH_upd_lt hs, bH_upd_lt hs⟩
  have hsucc : stS L (prH σ') (bH G σ') (η / G) ε ((σ').k) =
      stepS (L := L) (pr := prH σ') (b := bH G σ') (η := η / G) (ε := ε) σ.k S := by
    show stS L (prH σ') (bH G σ') (η / G) ε (σ.k + 1) = _
    rw [stS, hS']
  have hkL : τ.kL = S.1 := hR.2.1
  have hlw : ∀ f, ∀ ℓ ≤ L, lwOf τ f ℓ = S.2 f ℓ := hR.2.2
  have hmw : ∀ f (ℓ : Fin (L + 1)), mw (η / G) ε (fun _ => S.1) (fun _ => S.2) σ.k f ℓ = mwT η ε G τ f ℓ := by
    intro f ℓ; simp only [mw, mwT, hkL, hlw f ℓ (Nat.lt_succ_iff.1 ℓ.2)]
  have hne : (prH σ' σ.k).Nonempty := ⟨none, by rw [prH_upd_k]; simp [Pk]⟩
  have hinc : inc L (prH σ') (bH G σ') (η / G) ε (fun _ => S.1) (fun _ => S.2) σ.k =
      incT η ε L N G γ wE τ V ch bit := by
    have hmA : mA L (prH σ') (η / G) ε (fun _ => S.1) (fun _ => S.2) σ.k = mAT η ε L G τ V := by
      unfold mA mAT; rw [prH_upd_k]
      exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun ℓ _ => hmw f ℓ
    have hmA' : mA' L (prH σ') (bH G σ') (η / G) ε (fun _ => S.1) (fun _ => S.2) σ.k =
        mA'T η ε L N G γ wE τ V ch bit := by
      unfold mA' mA'T; rw [prH_upd_k, bH_upd_k hG hI hR hV hk]
      exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun ℓ _ => by rw [hmw f ℓ]
    unfold inc incT
    rw [if_pos hne, hmA, hmA']
  refine ⟨by show τ.k + 1 = σ.k + 1; rw [hR.1], ?_, ?_⟩
  · show τ.kL + incT η ε L N G γ wE τ V ch bit = (stS L (prH σ') (bH G σ') (η / G) ε ((σ').k)).1
    rw [hsucc, stepS, hinc, hkL]
  · intro f ℓ hℓ
    show lwOf (updT η ε L N G γ wE τ V ch bit) f ℓ = (stS L (prH σ') (bH G σ') (η / G) ε ((σ').k)).2 f ℓ
    rw [hsucc, stepS, hinc, show lwOf (updT η ε L N G γ wE τ V ch bit) f ℓ =
        if f ∈ Pk V ∧ ¬ 2 ^ ℓ ∣ τ.k + 1 then ((lwOf τ f ℓ).1 + bT η ε L N G γ wE τ V ch bit f, (lwOf τ f ℓ).2)
        else (0, τ.kL + incT η ε L N G γ wE τ V ch bit) from rfl, hlw f ℓ hℓ, hkL, hR.1, prH_upd_k,
      bH_upd_k hG hI hR hV hk]

end step

end Pool.P0230
