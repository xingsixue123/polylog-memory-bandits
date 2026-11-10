import Pool.P0230.Core

/-!
# The abstract twin of the self-rounding ALG: integer data since wake and a grid log-normaliser

State `TS`: learner time `k`, grid index `kL`, the experts present at the last learner time `ent`, and for them the
per-level pair (integer loss since wake, grid index at wake) to be carried into the next learner time `dat`.
The level-`ℓ` data of expert `f` at the current learner time are `lwOf τ f ℓ` (carried if `f ∈ ent` and no new
level-`ℓ` block starts, else fresh `(0, kL)`), exactly P0102's `stepS`. Weights `exp(−(η/G)·C + ε(kL − kw))`.
-/

namespace Pool.P0230

open Real Finset Pool.P0019 Pool.P0089 Pool.P0102 Pool.P0212

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The abstract twin state. -/
structure TS (ι : Type) where
  k : ℕ
  kL : ℕ
  ent : Finset (Option ι)
  dat : Option ι → ℕ → ℕ × ℕ

/-- Experts present at a learner time with active set `V`: the meta-arm and the active copies. -/
def Pk (V : Finset ι) : Finset (Option ι) := insert none (V.map Function.Embedding.some)

theorem mem_Pk (V : Finset ι) (f : Option ι) : f ∈ Pk V ↔ presOf V f = true := by
  cases f with
  | none => simp [Pk, presOf]
  | some x => simp [Pk, presOf]

/-- The level-`ℓ` data of expert `f` at the twin's current learner time. -/
def lwOf (τ : TS ι) (f : Option ι) (ℓ : ℕ) : ℕ × ℕ :=
  if f ∈ τ.ent ∧ ¬ 2 ^ ℓ ∣ τ.k then τ.dat f ℓ else (0, τ.kL)

variable (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ)

/-- Twin weight of the level-`ℓ` specialist of `f`. -/
noncomputable def mwT (τ : TS ι) (f : Option ι) (ℓ : ℕ) : ℝ :=
  exp (-(η / G) * ((lwOf τ f ℓ).1 : ℝ) + ε * ((τ.kL : ℝ) - ((lwOf τ f ℓ).2 : ℝ)))

/-- Twin awake mass. -/
noncomputable def mAT (τ : TS ι) (V : Finset ι) : ℝ := ∑ f ∈ Pk V, ∑ ℓ : Fin (L + 1), mwT η ε G τ f ℓ

/-- Twin marginal over experts. -/
noncomputable def pmargT (τ : TS ι) (V : Finset ι) (f : Option ι) : ℝ :=
  if f ∈ Pk V then (∑ ℓ : Fin (L + 1), mwT η ε G τ f ℓ) / mAT η ε L G τ V else 0

/-- The draw of a marginal `p` (P0179's coin realization; the meta-arm if `p` is not a distribution). -/
noncomputable def drawOf (p : Option ι → ℝ) (d : Fin N) : Option ι :=
  open Classical in
  if h : (∀ f, 0 ≤ p f) ∧ ∑ f, p f = 1 then Pool.P0179.draw (N := N) (b := (none : Option ι)) h.1 h.2 d else none

theorem drawA_eq_drawOf (σ : AState ι) (V : Finset ι) (d : Fin N) :
    drawA η L N σ V d = drawOf N (pmarg η L σ V) d := rfl

/-- Integer IX loss of expert `f` for the marginal `p`, draw `ch` and loss bit `bit`. -/
noncomputable def bOfP (p : Option ι → ℝ) (ch : Option ι) (bit : Bool) (f : Option ι) : ℕ :=
  if f = ch then ⌊(G : ℝ) * ((bit.toNat : ℝ) / (wE * (Pool.P0179.pt N none p f + γ)))⌋₊ else 0

theorem ixA_eq_bOfP (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) (f : Option ι) :
    ixA η L N G γ wE σ V ch bit f = (bOfP N G γ wE (pmarg η L σ V) ch bit f : ℝ) / G := by
  unfold ixA bOfP ptA
  split_ifs <;> simp

/-- Twin integer IX losses. -/
noncomputable def bT (τ : TS ι) (V : Finset ι) (ch : Option ι) (bit : Bool) (f : Option ι) : ℕ :=
  bOfP N G γ wE (pmargT η ε L G τ V) ch bit f

/-- Twin awake mass after the exponential update. -/
noncomputable def mA'T (τ : TS ι) (V : Finset ι) (ch : Option ι) (bit : Bool) : ℝ :=
  ∑ f ∈ Pk V, ∑ ℓ : Fin (L + 1), mwT η ε G τ f ℓ * exp (-(η / G) * (bT η ε L N G γ wE τ V ch bit f : ℝ))

/-- Twin grid increment. -/
noncomputable def incT (τ : TS ι) (V : Finset ι) (ch : Option ι) (bit : Bool) : ℕ :=
  ⌊log (mAT η ε L G τ V / mA'T η ε L N G γ wE τ V ch bit) / ε⌋₊

/-- Twin update on an exploitation round. -/
noncomputable def updT (τ : TS ι) (V : Finset ι) (ch : Option ι) (bit : Bool) : TS ι where
  k := τ.k + 1
  kL := τ.kL + incT η ε L N G γ wE τ V ch bit
  ent := Pk V
  dat f ℓ := ((lwOf τ f ℓ).1 + bT η ε L N G γ wE τ V ch bit f, (lwOf τ f ℓ).2)

/-- The initial twin state. -/
def t0 : TS ι := ⟨0, 0, ∅, fun _ _ => (0, 0)⟩

end Pool.P0230
