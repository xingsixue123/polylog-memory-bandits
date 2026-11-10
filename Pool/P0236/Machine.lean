import Pool.P0236.Enc
import Pool.P0236.Swap
import Pool.P0215.Interval

/-!
# The finite-state twin as P0194's ALG, and the simulation of the self-rounding ALG on fitting runs

`withTwin` is P0194's parameters with the FINITE twin state `FS` (P0225's `withAlgG … ρStar` with its ALG swapped).
On every run on which every active set before `T` has at most `S − 1` copies (and `T ≤ 2^L`, `T ≤ KM`, P0215's
level hypotheses), its ALG choices, plays and policy losses before `T` are those of `withAlgG … ρStar`.
-/

namespace Pool.P0236

open Pool.P0230 Real Finset Pool.P0019 Pool.P0089 Pool.P0102 Pool.P0212 Pool.P0194 Pool.P0001

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem card_Pk (V : Finset ι) : (Pk V).card = V.card + 1 := by
  rw [Pk, Finset.card_insert_of_notMem (by simp), Finset.card_map]

/-- The twin draws only active copies or the meta-arm. -/
theorem drawOf_mem (η ε : ℝ) (L N G : ℕ) (τ : TS ι) (V : Finset ι) (d : Fin N) (x : ι)
    (h : drawOf N (pmargT η ε L G τ V) d = some x) : x ∈ V := by
  classical
  by_contra hx
  unfold drawOf at h
  split_ifs at h with hp
  have hcard := Pool.P0179.card_draw_fiber (N := N) (b := (none : Option ι)) hp.1 hp.2 (some x)
  have hc0 : Pool.P0179.cnt N none (pmargT η ε L G τ V) (some x) = 0 := by
    unfold Pool.P0179.cnt
    rw [if_neg (by simp)]
    have : pmargT η ε L G τ V (some x) = 0 := by
      unfold pmargT; rw [if_neg]; rw [mem_Pk]; simpa [presOf] using hx
    rw [this, zero_mul, Nat.floor_zero]
  rw [hc0, Finset.card_eq_zero] at hcard
  have : d ∈ (univ.filter fun k : Fin N => Pool.P0179.draw (N := N) (b := (none : Option ι)) hp.1 hp.2 k = some x) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; convert h
  rw [hcard] at this
  simp at this

end Pool.P0236

namespace Pool.P0236

open Pool.P0230 Real Finset Pool.P0019 Pool.P0089 Pool.P0102 Pool.P0212 Pool.P0194 Pool.P0001

variable {ι : Type} [Fintype ι] {n : ℕ} [LinearOrder ι]

/-- Cap on the integer IX losses. -/
noncomputable def Bmx (G : ℕ) (γ wE : ℝ) : ℕ := ⌊(G : ℝ) / (wE * γ)⌋₊

/-- Cap on the grid increment. -/
noncomputable def Imx (η ε : ℝ) (G : ℕ) (γ wE : ℝ) : ℕ := ⌊η / G * (Bmx G γ wE : ℝ) / ε⌋₊

/-- **P0194's parameters with the finite-state twin ALG** (`S` entries, learner times `≤ KM`). -/
noncomputable def withTwin (P : ParD n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (S KM : ℕ) : ParD n ι :=
  swapA (Pool.P0225.withAlgG P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε))
    (FS ι L S KM (KM * Imx η ε G γ wE) (KM * Bmx G γ wE)) (enc t0)
    (fun φ V d => drawOf N (pmargT η ε L G (dec φ) V) d)
    (fun φ V _ ch bit => enc (updT η ε L N G γ wE (dec φ) V ch bit))
    (fun φ V d x h => drawOf_mem η ε L N G (dec φ) V d x h)

/-- The finite twin's state count. -/
theorem card_withTwin (P : ParD n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (S KM : ℕ) :
    Fintype.card (FS ι L S KM (KM * Imx η ε G γ wE) (KM * Bmx G γ wE)) ≤
      (KM + 1) * (KM * Imx η ε G γ wE + 1) *
        ((Fintype.card ι + 1) * ((KM * Bmx G γ wE + 1) * (KM * Imx η ε G γ wE + 1)) ^ (L + 1) + 1) ^ S :=
  card_FS ι L S KM _ _

section sim

variable {η ε : ℝ} {L N G : ℕ} {γ wE : ℝ} {S KM : ℕ}

/-- The simulation relation: invariants, the twin relation for the decoded state, integer losses `≤ Bmx`. -/
def RelF (σ : AState ι) (φ : FS ι L S KM (KM * Imx η ε G γ wE) (KM * Bmx G γ wE)) : Prop :=
  Inv η ε L G σ ∧ Rel η ε L G σ (dec φ) ∧ ∀ t < σ.k, ∀ f, bH G σ t f ≤ Bmx G γ wE

/-- The rounds where the simulation step is valid. -/
def GoodF (σ : AState ι) (V : Finset ι) : Prop :=
  HentV σ V ∧ σ.k < 2 ^ L ∧ V.card + 1 ≤ S ∧ σ.k + 1 ≤ KM

theorem relF_start (hε : 0 < ε) (hη : 0 ≤ η) :
    RelF (η := η) (ε := ε) (L := L) (G := G) (γ := γ) (wE := wE) (S := S) (KM := KM) (s0A : AState ι) (enc t0) := by
  refine ⟨inv_s0A, ?_, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  have h := dec_enc (S := S) (KM := KM) (L := L) (KLM := KM * Imx η ε G γ wE) (CM := KM * Bmx G γ wE)
    (τ := (t0 : TS ι)) (by simp [t0]) (by simp [t0]) (by simp [t0]) (by simp [t0])
  exact rel_congr rel_s0A h.1 h.2.1 h.2.2

theorem draw_sim (hG : 0 < G) {σ : AState ι} {φ : FS ι L S KM (KM * Imx η ε G γ wE) (KM * Bmx G γ wE)}
    {V : Finset ι} (hR : RelF σ φ) (hg : GoodF (L := L) (S := S) (KM := KM) σ V) (d : Fin N) :
    drawA η L N σ V d = drawOf N (pmargT η ε L G (dec φ) V) d :=
  (drawOf_pmargT hG hR.1 hR.2.1 hg.1 hg.2.1 d).symm

theorem upd_sim (hG : 0 < G) (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η) {σ : AState ι}
    {φ : FS ι L S KM (KM * Imx η ε G γ wE) (KM * Bmx G γ wE)} {V : Finset ι} (hR : RelF σ φ)
    (hg : GoodF (L := L) (S := S) (KM := KM) σ V) (d : Fin N) (ch : Option ι) (bit : Bool) :
    RelF (Pool.P0225.updAG η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) σ V d ch bit)
      (enc (S := S) (KM := KM) (L := L) (KLM := KM * Imx η ε G γ wE) (CM := KM * Bmx G γ wE)
        (updT η ε L N G γ wE (dec φ) V ch bit)) := by
  obtain ⟨hI, hRel, hbd⟩ := hR
  obtain ⟨hV, hk, hS, hKM⟩ := hg
  set σ' := Pool.P0225.updAG η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) σ V d ch bit with hσ'
  set τ' := updT η ε L N G γ wE (dec φ) V ch bit with hτ'
  have hI' : Inv η ε L G σ' := inv_upd hG hI hRel hV hk
  have hR' : Rel η ε L G σ' τ' := rel_upd hG hI hRel hV hk
  -- integer losses of the new state are `≤ Bmx`
  have hbd' : ∀ t < σ'.k, ∀ f, bH G σ' t f ≤ Bmx G γ wE := by
    intro t ht f
    rcases Nat.lt_or_ge t σ.k with h | h
    · rw [bH_upd_lt h]; exact hbd t h f
    · have : t = σ.k := by have : σ'.k = σ.k + 1 := rfl; omega
      subst this
      rw [bH_upd_k hG hI hRel hV hk]
      exact bOfP_le N G hγ hwE _ ch bit f
  -- the integer run of the new state stays below the caps
  have hrun := stS_le L (prH σ') (bH G σ') (η / G) ε (Bm := Bmx G γ wE) (div_nonneg hη (Nat.cast_nonneg _)) hε
    σ'.k hbd'
  have hrun0 := stS_le L (prH σ) (bH G σ) (η / G) ε (Bm := Bmx G γ wE) (div_nonneg hη (Nat.cast_nonneg _)) hε
    σ.k hbd
  have hk' : σ'.k = σ.k + 1 := rfl
  have hkL' : τ'.kL ≤ KM * Imx η ε G γ wE := by
    rw [hR'.2.1]
    refine hrun.1.trans ?_
    rw [hk']
    exact Nat.mul_le_mul_right _ hKM
  have hdat : ∀ f ∈ τ'.ent, ∀ ℓ ≤ L, (τ'.dat f ℓ).1 ≤ KM * Bmx G γ wE ∧ (τ'.dat f ℓ).2 ≤ KM * Imx η ε G γ wE := by
    intro f _ ℓ hℓ
    have hlw := hRel.2.2 f ℓ hℓ
    have hb : bOfP N G γ wE (pmargT η ε L G (dec φ) V) ch bit f ≤ Bmx G γ wE :=
      bOfP_le N G hγ hwE (pmargT η ε L G (dec φ) V) ch bit f
    obtain ⟨h1, h2⟩ := hrun0.2 f ℓ
    show (lwOf (dec φ) f ℓ).1 + bT η ε L N G γ wE (dec φ) V ch bit f ≤ KM * Bmx G γ wE ∧
      (lwOf (dec φ) f ℓ).2 ≤ KM * Imx η ε G γ wE
    rw [hlw]
    unfold bT
    constructor
    · have : (σ.k + 1) * Bmx G γ wE ≤ KM * Bmx G γ wE := Nat.mul_le_mul_right _ hKM
      unfold lwr; rw [Nat.succ_mul] at this; omega
    · have : σ.k * Imx η ε G γ wE ≤ KM * Imx η ε G γ wE := Nat.mul_le_mul_right _ (by omega)
      unfold lwr; unfold Imx; exact h2.trans (hrun0.1.trans this)
  have hdec := dec_enc (S := S) (KM := KM) (L := L) (KLM := KM * Imx η ε G γ wE) (CM := KM * Bmx G γ wE) (τ := τ')
    (by show (Pk V).card ≤ S; rw [card_Pk]; exact hS)
    (by show (dec φ).k + 1 ≤ KM; rw [hRel.1]; exact hKM) hkL' hdat
  exact ⟨hI', rel_congr hR' hdec.1 hdec.2.1 hdec.2.2, hbd'⟩

end sim

end Pool.P0236
