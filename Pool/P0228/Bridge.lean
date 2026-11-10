import Pool.P0228.ExpD
import Pool.P0217.Regret

/-! P0217's `slotT` is the per-round form bounded in `Pool.P0228.slot_expect` (definitional). -/

open Finset Pool.P0001 Pool.P0050 Pool.P0201 Pool.P0194

namespace Pool.P0228

/-- **Bridge.** P0217's `slotT` (for fixed sampling/filter array `arr`) is `Σ_{u<T} E_{coins<u}[probeU_u]` with
P0217's shifted losses and the array's sampling and filter bits. -/
theorem slotT_eq {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : MPar n ι) (T : ℕ)
    (ℓ : LossSeq n) (rc₀ : RC m.P) (arr : Pool.P0116.Arr (Pool.P0201.pp m) T → Bool) :
    Pool.P0217.slotT m T ℓ rc₀ arr =
      ∑ u ∈ range T, ∑ ω' : Fin u → RC m.P, Pool.P0202.pw (wR m.P) ω' *
        probeU m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
          (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) (Pool.P0210.extR m.P rc₀ ω') u := rfl

end Pool.P0228
