import Pool.P0194.Proc
import Pool.P0202.Proc194

/-!
# P0194: the expected loss over `T` rounds as a sum of per-round weighted losses, and the regret split
-/

open Finset Pool.P0001 Pool.P0194

namespace Pool.P0210

attribute [local instance] Pool.P0050.CoinAlg.fS Pool.P0050.CoinAlg.fY Pool.P0050.CoinAlg.fZ

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- A finite coin sequence extended by a default round coin. -/
def extR (rc₀ : RC P) {t : ℕ} (ω' : Fin t → RC P) : ℕ → RC P := fun v => if h : v < t then ω' ⟨v, h⟩ else rc₀

theorem extR_lt (rc₀ : RC P) {t : ℕ} (ω' : Fin t → RC P) (v : ℕ) (hv : v < t) : extR P rc₀ ω' v = ω' ⟨v, hv⟩ := by
  simp [extR, hv]

/-- The extension of a prefix agrees with the extension of the whole sequence before the prefix length. -/
theorem agree_pre (rc₀ : RC P) {u T : ℕ} (h : u ≤ T) (ω : Fin T → RC P) :
    Agree P (extR P rc₀ (Pool.P0202.pre h ω)) (extR P rc₀ ω) u := by
  intro v hv
  simp [extR, hv, show v < T by omega, Pool.P0202.pre]

theorem agree_snoc (rc₀ : RC P) {u : ℕ} (ω' : Fin u → RC P) (z : RC P) :
    Agree P (extR P rc₀ (Fin.snoc ω' z : Fin (u + 1) → RC P)) (Function.update (extR P rc₀ ω') u z) (u + 1) := by
  intro v hv
  rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
  · rw [Function.update_of_ne (by omega)]
    simp only [extR, hv, show v < u + 1 by omega, ↓reduceDIte]
    exact Fin.snoc_castSucc (α := fun _ => RC P) (p := ω') (x := z) (i := ⟨v, hv⟩)
  · rw [Function.update_self]
    simp only [extR, show v < v + 1 by omega, ↓reduceDIte]
    exact Fin.snoc_last (α := fun _ => RC P) (p := ω') (x := z)

/-- **One round.** The `wR`-weighted loss of round `u < T` over `T` i.i.d. round coins is the weighted average, over
the coins before `u`, of P0194's `condLoss`. -/
theorem expect_loss_round (hL : P.IsLaw) (hN : 0 < P.N) (rc₀ : RC P) {u T : ℕ} (hu : u < T) :
    ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * ((ℓ u (play P ℓ (extR P rc₀ ω) ωs φ u)).toNat : ℝ) =
      ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' * condLoss P ℓ ωs φ (extR P rc₀ ω') u := by
  have h1 : ∑ rc, wR P rc = 1 := sum_wR P hL hN
  have hpre : ∀ ω : Fin T → RC P, play P ℓ (extR P rc₀ ω) ωs φ u =
      play P ℓ (extR P rc₀ (Pool.P0202.pre hu ω)) ωs φ u := fun ω =>
    (play_congr ωs φ u (agree_pre P rc₀ hu ω)).symm
  simp_rw [hpre]
  rw [Pool.P0202.sum_pw_prefix h1 (u + 1)
    (fun ω'' => ((ℓ u (play P ℓ (extR P rc₀ ω'') ωs φ u)).toNat : ℝ)) T hu, Pool.P0202.sum_snoc_pw]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  congr 1
  unfold condLoss
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [play_congr ωs φ u (agree_snoc P rc₀ ω' z)]

/-- **Summed.** The expected loss over `T` rounds is the sum over rounds of the expected `condLoss`. -/
theorem expect_loss_eq (hL : P.IsLaw) (hN : 0 < P.N) (rc₀ : RC P) (T : ℕ) :
    ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
        ∑ u ∈ range T, ((ℓ u (play P ℓ (extR P rc₀ ω) ωs φ u)).toNat : ℝ) =
      ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' * condLoss P ℓ ωs φ (extR P rc₀ ω') u := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu => ?_
  exact expect_loss_round P ℓ ωs φ hL hN rc₀ (Finset.mem_range.1 hu)

theorem sum_slot_weights : ∑ s : Σ j : Fin P.D, Fin (P.sl j), P.xr s.1 = ∑ j, (P.sl j : ℝ) * P.xr j := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- The per-round regret split: under `ParD.IsLaw`, `condLoss − ℓ_u(i)` is the weighted sum of BASE's, ALG's and the
slots' gaps to `ℓ_u(i)`. -/
theorem condLoss_sub (hL : P.IsLaw) (hN : 0 < P.N) (ω : ℕ → RC P) (u : ℕ) (c : ℝ) :
    condLoss P ℓ ωs φ ω u - c = P.wB * (bPol P ℓ ω u - c) + P.wE * (aPol P ℓ ωs φ ω u - c) +
      ∑ s : Σ j : Fin P.D, Fin (P.sl j), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - c) := by
  rw [condLoss_eq P ℓ ωs φ hN ω u]
  have hw : P.wB + P.wE + ∑ s : Σ j : Fin P.D, Fin (P.sl j), P.xr s.1 = 1 := by
    rw [sum_slot_weights]; exact hL.2.2.2
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  linear_combination c * hw

/-- **Regret split (C9, first step, for P0194).** Under `ParD.IsLaw`, the expected regret of P0194's process over `T`
rounds against a fixed arm `i` (round coins i.i.d. with weights `wR`, sampling/filter bits fixed) is the sum over rounds
of the expected weighted gaps of BASE (`wB`), ALG (`wE`) and every slot (`x_{thread}`) to `ℓ_u(i)`. -/
theorem regret_split (hL : P.IsLaw) (hN : 0 < P.N) (rc₀ : RC P) (T : ℕ) (i : Fin n) :
    ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
        ∑ u ∈ range T, ((ℓ u (play P ℓ (extR P rc₀ ω) ωs φ u)).toNat : ℝ) -
      ∑ u ∈ range T, ((ℓ u i).toNat : ℝ) =
      ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
        (P.wB * (bPol P ℓ (extR P rc₀ ω') u - (ℓ u i).toNat) +
          P.wE * (aPol P ℓ ωs φ (extR P rc₀ ω') u - (ℓ u i).toNat) +
          ∑ s : Σ j : Fin P.D, Fin (P.sl j), P.xr s.1 * (slotVal P ℓ ωs φ (extR P rc₀ ω') u s - (ℓ u i).toNat)) := by
  have h1 : ∑ rc, wR P rc = 1 := sum_wR P hL hN
  rw [expect_loss_eq P ℓ ωs φ hL hN rc₀ T, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hone : ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' = 1 := Pool.P0202.sum_pw_one h1 u
  calc ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' * condLoss P ℓ ωs φ (extR P rc₀ ω') u - ((ℓ u i).toNat : ℝ)
      = ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
          (condLoss P ℓ ωs φ (extR P rc₀ ω') u - ((ℓ u i).toNat : ℝ)) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hone, one_mul]
    _ = _ := by
        refine Finset.sum_congr rfl fun ω' _ => ?_
        rw [condLoss_sub P ℓ ωs φ hL hN]

/-- **Regret split, regrouped against BASE (the form the C9 assembly pairs with P0202 and the probing lemmas).** On
empty or retired slots `slotVal = bPol`, so in `regret_split` some of BASE's plays sit inside the slot term. Writing
`slotVal − ℓ_u(i) = (slotVal − bPol) + (bPol − ℓ_u(i))` gives BASE its total weight `wB + Σ_s x_{thread s}`, ALG `wE`,
and each slot only its gap to BASE's policy loss (zero on empty or retired slots). -/
theorem regret_split_base (hL : P.IsLaw) (hN : 0 < P.N) (rc₀ : RC P) (T : ℕ) (i : Fin n) :
    ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
        ∑ u ∈ range T, ((ℓ u (play P ℓ (extR P rc₀ ω) ωs φ u)).toNat : ℝ) -
      ∑ u ∈ range T, ((ℓ u i).toNat : ℝ) =
      ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
        ((P.wB + ∑ s : Σ j : Fin P.D, Fin (P.sl j), P.xr s.1) * (bPol P ℓ (extR P rc₀ ω') u - (ℓ u i).toNat) +
          P.wE * (aPol P ℓ ωs φ (extR P rc₀ ω') u - (ℓ u i).toNat) +
          ∑ s : Σ j : Fin P.D, Fin (P.sl j), P.xr s.1 *
            (slotVal P ℓ ωs φ (extR P rc₀ ω') u s - bPol P ℓ (extR P rc₀ ω') u)) := by
  rw [regret_split P ℓ ωs φ hL hN rc₀ T i]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun ω' _ => ?_
  congr 1
  have h : ∀ s : Σ j : Fin P.D, Fin (P.sl j), P.xr s.1 * (slotVal P ℓ ωs φ (extR P rc₀ ω') u s - (ℓ u i).toNat) =
      P.xr s.1 * (slotVal P ℓ ωs φ (extR P rc₀ ω') u s - bPol P ℓ (extR P rc₀ ω') u) +
        P.xr s.1 * (bPol P ℓ (extR P rc₀ ω') u - (ℓ u i).toNat) := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => h s, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

end Pool.P0210
