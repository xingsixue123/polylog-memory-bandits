import Pool.P0284.Memory
import Pool.P0281.TwinArr
import Pool.P0282.MargBound
import Pool.P0287.Overflow

/-!
# The ALG term of the one-level machine (P0262's F7: P0281's bound instantiated for P0284's family)
-/

namespace Pool.P0290

open Finset Pool.P0261 Pool.P0284 Pool.P0194

variable (n T : ℕ) [NeZero n] (q : ℝ) (A : Pool.P0050.CoinAlg n) {T' Kc : ℕ}

/-- The grid copy of arm `i` entering thread `j` at round `a` (P0121's index `a·(D·n) + j·n + i`), when that is a
grid point before `Tp`; copy `0` otherwise. -/
def cstarF (i : Fin n) (j a : ℕ) : CpG n (Tp T) :=
  if h : j < Dn (Tp T) ∧ a < Tp T ∧ Bt (Tp T) j ∣ a then
    ⟨⟨a * (Dn (Tp T) * n) + j * n + i.1, by
      have h1 : j * n + i.1 < Dn (Tp T) * n := by
        have := i.2; nlinarith [h.1]
      have h2 : a * (Dn (Tp T) * n) + Dn (Tp T) * n ≤ Tp T * (Dn (Tp T) * n) := by
        have : a + 1 ≤ Tp T := h.2.1
        calc a * (Dn (Tp T) * n) + Dn (Tp T) * n = (a + 1) * (Dn (Tp T) * n) := by ring
          _ ≤ Tp T * (Dn (Tp T) * n) := Nat.mul_le_mul_right _ this
      have : Tp T * Dn (Tp T) * n = Tp T * (Dn (Tp T) * n) := by ring
      omega⟩, by
        show Bt (Tp T) ((a * (Dn (Tp T) * n) + j * n + i.1) / n % Dn (Tp T)) ∣
          (a * (Dn (Tp T) * n) + j * n + i.1) / (Dn (Tp T) * n)
        have hn : 0 < n := NeZero.pos n
        have e1 : (a * (Dn (Tp T) * n) + j * n + i.1) / (Dn (Tp T) * n) = a := by
          rw [show a * (Dn (Tp T) * n) + j * n + i.1 = (j * n + i.1) + (Dn (Tp T) * n) * a by ring,
            Nat.add_mul_div_left _ _ (Nat.mul_pos (by unfold Dn; omega) hn)]
          have : (j * n + i.1) / (Dn (Tp T) * n) = 0 := Nat.div_eq_of_lt (by have := i.2; nlinarith [h.1])
          omega
        have e2 : (a * (Dn (Tp T) * n) + j * n + i.1) / n % Dn (Tp T) = j := by
          rw [show a * (Dn (Tp T) * n) + j * n + i.1 = i.1 + n * (a * Dn (Tp T) + j) by ring,
            Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt i.2, zero_add,
            show a * Dn (Tp T) + j = j + Dn (Tp T) * a by ring, Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt h.1
        rw [e1, e2]; exact h.2.2⟩
  else ⟨⟨0, by
            have h1 := Tp_pos T
            have h2 : 0 < Dn (Tp T) := by unfold Dn; omega
            have h3 := NeZero.pos n
            exact Nat.mul_pos (Nat.mul_pos h1 h2) h3⟩, by
          show Bt (Tp T) (0 / n % Dn (Tp T)) ∣ 0 / (Dn (Tp T) * n); simp⟩

theorem cstarF_val (i : Fin n) {j a : ℕ} (hj : j < Dn (Tp T)) (ha : a < Tp T) (hd : Bt (Tp T) j ∣ a) :
    ((cstarF n T i j a).1 : ℕ) = a * (Dn (Tp T) * n) + j * n + i.1 := by
  unfold cstarF; rw [dif_pos ⟨hj, ha, hd⟩]

theorem cstarF_E (i : Fin n) {j a : ℕ} (hj : j < Dn (Tp T)) (ha : a < Tp T) (hd : Bt (Tp T) j ∣ a) :
    Pool.P0121.TM.E n (Tp T) (Dn (Tp T)) (cstarF n T i j a).1 = a := by
  unfold Pool.P0121.TM.E; rw [cstarF_val n T i hj ha hd]
  have hn : 0 < n := NeZero.pos n
  rw [show a * (Dn (Tp T) * n) + j * n + i.1 = (j * n + i.1) + (Dn (Tp T) * n) * a by ring,
    Nat.add_mul_div_left _ _ (Nat.mul_pos (by unfold Dn; omega) hn)]
  have : (j * n + i.1) / (Dn (Tp T) * n) = 0 := Nat.div_eq_of_lt (by have := i.2; nlinarith)
  omega

theorem cstarF_thr (i : Fin n) {j a : ℕ} (hj : j < Dn (Tp T)) (ha : a < Tp T) (hd : Bt (Tp T) j ∣ a) :
    Pool.P0121.TM.thr0 n (Tp T) (Dn (Tp T)) (cstarF n T i j a).1 = j := by
  unfold Pool.P0121.TM.thr0; rw [cstarF_val n T i hj ha hd]
  have hn : 0 < n := NeZero.pos n
  rw [show a * (Dn (Tp T) * n) + j * n + i.1 = i.1 + n * (a * Dn (Tp T) + j) by ring,
    Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt i.2, zero_add,
    show a * Dn (Tp T) + j = j + Dn (Tp T) * a by ring, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hj

theorem cstarF_arm (i : Fin n) {j a : ℕ} (hj : j < Dn (Tp T)) (ha : a < Tp T) (hd : Bt (Tp T) j ∣ a) :
    Pool.P0121.TM.arm n (Tp T) (Dn (Tp T)) (cstarF n T i j a).1 = i := by
  unfold Pool.P0121.TM.arm; ext; simp only
  rw [cstarF_val n T i hj ha hd]
  rw [show a * (Dn (Tp T) * n) + j * n + i.1 = i.1 + n * (a * Dn (Tp T) + j) by ring, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt i.2

section Basic

theorem Lx_pos : 0 < Lx n T := by
  unfold Lx
  have h1 : 0 ≤ Real.log ((Tp T : ℝ) + 1) := Real.log_nonneg (by have : (0 : ℝ) ≤ Tp T := Nat.cast_nonneg _; linarith)
  have h2 : 0 < Real.log (4 * (Fintype.card (CpG n (Tp T)) : ℝ) + 4) := Real.log_pos (by
    have : (0 : ℝ) ≤ Fintype.card (CpG n (Tp T)) := Nat.cast_nonneg _; linarith)
  linarith

theorem xf_pos (hK : 1 ≤ Kc) : 0 < Pool.P0282.xf n T' Kc := by
  unfold Pool.P0282.xf
  have : (0 : ℝ) < ((max Kc (Bm n T') : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le hK (le_max_left _ _)
  positivity

theorem xf_le_one (hK : 1 ≤ Kc) : Pool.P0282.xf n T' Kc ≤ 1 := by
  unfold Pool.P0282.xf
  rw [div_le_one (by exact_mod_cast lt_of_lt_of_le hK (le_max_left _ _))]
  exact_mod_cast le_trans hK (le_max_left _ _)

theorem one_div_xf (hK : 1 ≤ Kc) : 1 / Pool.P0282.xf n T' Kc = (max Kc (Bm n T') : ℕ) := by
  unfold Pool.P0282.xf; rw [one_div_one_div]

theorem ηA_le_one : ηA n T q ≤ 1 := by
  unfold ηA; rw [div_le_one (lt_of_lt_of_le one_pos (le_max_left _ _))]; exact le_max_left _ _

theorem Bt_pred_le (T' i : ℕ) (hi : 1 ≤ i) : (Bt T' (i - 1) : ℝ) ≤ 2 * Bt T' i := by
  have : Bt T' (i - 1) ≤ 2 * Bt T' i := by
    unfold Bt
    rcases Nat.lt_or_ge (Dp T') i with h | h
    · rw [show Dp T' - i = 0 by omega]
      have : Dp T' - (i - 1) = 0 := by omega
      rw [this]; norm_num
    · rw [show Dp T' - (i - 1) = (Dp T' - i) + 1 by omega, pow_succ]; omega
  exact_mod_cast this

end Basic

/-- P0268's capped margins do not read the ALG's rounding `ρG`. -/
theorem ΛPc_ρG {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ)
    (ρG ρG' : Pool.P0212.AState ι → Finset ι → Option ι → Bool → ℝ) (T' : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ)
    (Θn j m : ℕ) :
    Pool.P0268.ΛPc P η L N G γ wE ρG T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn j m =
      Pool.P0268.ΛPc P η L N G γ wE ρG' T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn j m := rfl

/-- P0275's `margP_hΛ'` with the roundings of the margins, of the walk's process and of `ΛPc` independent (none of
them is read by the margins). -/
theorem margP_hΛ'_gen {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ)
    (ρ1 ρ2 ρ3 : Pool.P0212.AState ι → Finset ι → Option ι → Bool → ℝ) (T' : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ)
    (Θn : ℕ) : ∀ c u,
    Pool.P0268.ΛPc (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ3 T' δ
      Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn
      (min (Pool.P0065.curT
        (Pool.P0225.withAlgG (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ2).E
        (Pool.P0225.withAlgG (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ2).thr0
        (Pool.P0225.withAlgG (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ2).D
        (Pool.P0225.withAlgG (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ2).Bt
        c (u + 1))
        ((Pool.P0225.withAlgG (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ2).D - 1))
      (u + 1 - (Pool.P0225.withAlgG (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE
        ρ2).E c) ≤
    (Pool.P0225.withAlgG (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ2).Λ c u :=
  fun _ _ => le_rfl

/-- The self-rounding ALG's rounding as P0284's `P1` builds it (decidable equality of the subtype). -/
noncomputable abbrev ρSub : Pool.P0212.AState (CpG n (Tp T)) → Finset (CpG n (Tp T)) → Option (CpG n (Tp T)) →
    Bool → ℝ :=
  Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q)

section Inst

attribute [local instance] Pool.P0082.coinFintype

/-- Decidable equality of the grid copies from their order (the instance P0281/P0245 use for a generic `ι`). -/
abbrev decCpG (n T : ℕ) [NeZero n] : DecidableEq (CpG n T) :=
  fun a b => LinearOrder.toDecidableEq a b

attribute [scoped instance high] decCpG

open Pool.P0250 (AP BP ccP)

/-- The coarse threads of P0259's split: epochs `≥ Tp/n`. -/
def czF (j : ℕ) : Prop := Tp T ≤ n * Bt (Tp T) j

scoped instance czF_dec (j : ℕ) : Decidable (czF n T j) := by unfold czF; infer_instance

/-- The self-rounding ALG's process of P0281 at `famM` (`QQ` of P0281 with `M0 := P0284.M0`). -/
noncomputable abbrev QM : ParD n (CpG n (Tp T)) :=
  Pool.P0236.PG (M0 n T q A).P (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)

/-- `AP` at `famM`'s constants. -/
noncomputable abbrev APF : ℝ :=
  AP (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q)) (Tp T)
    (εA n T q) (Lx n T) (Lx n T) (Lx n T) (ηA n T q) (Pool.P0282.xf n (Tp T) (KcF n T q)) (KcF n T q) 2 n (Tp T)
    (Dp (Tp T))

/-- `BP` at `famM`'s constants. -/
noncomputable abbrev BPF : ℝ :=
  BP (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q)) (Lx n T)
    (KcF n T q)

/-- P0281's walk weight cap `Mw = 2·(AP + BP·√(Tp/n))`. -/
noncomputable def MwF : ℝ := 2 * (APF n T q A + BPF n T q A * Real.sqrt ((Tp T : ℝ) / n))

theorem hΛ'_F : ∀ c u, Pool.P0268.ΛPc (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
      (wEA n T q A) (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q))
      (Tp T) (εA n T q) (Lx n T) (Lx n T) (Lx n T) (Lx n T) (ηA n T q) (Pool.P0282.xf n (Tp T) (KcF n T q))
      (KcF n T q) 2 n (Tp T) (Dp (Tp T)) (Dp (Tp T))
        (min (Pool.P0065.curT (QM n T q A).E (QM n T q A).thr0 (QM n T q A).D (QM n T q A).Bt c (u + 1))
          ((QM n T q A).D - 1)) (u + 1 - (QM n T q A).E c) ≤ (QM n T q A).Λ c u :=
  margP_hΛ'_gen n (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (ρSub n T q A)
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q))
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q))
    (Tp T) (εA n T q) (Lx n T) (Lx n T) (Lx n T) (Lx n T) (ηA n T q)
    (Pool.P0282.xf n (Tp T) (KcF n T q)) (KcF n T q) 2 n (Tp T) (Dp (Tp T)) (Dp (Tp T))

theorem hΘn_F : ∀ c, (QM n T q A).thr0 c ≤ Dp (Tp T) := fun c => by
  show Pool.P0121.TM.thr0 n (Tp T) (Dn (Tp T)) c.1 ≤ Dp (Tp T)
  unfold Pool.P0121.TM.thr0
  have hD0 : 0 < Dn (Tp T) := by unfold Dn; omega
  have := Nat.mod_lt (c.1 / n) hD0; have e : Dn (Tp T) = Dp (Tp T) + 1 := rfl; omega

theorem hΘ_F : ∀ c, ((QM n T q A).thr0 c : ℝ) ≤ Dp (Tp T) := fun c => by exact_mod_cast hΘn_F n T q A c

theorem hL_F (hq : 0 < q) (hq1 : q ≤ 1 / 32) : (QM n T q A).IsLaw := P0_isLaw n T q A hq hq1

theorem hx0_F (hn : 1 ≤ n) (hq : 0 < q) : 1 / Pool.P0191.xrN (QM n T q A).xr 0 ≤ (KcF n T q : ℝ) := by
  have hK := KcF_pos n T q hq
  have hD0 : 0 < (QM n T q A).D := by show 0 < Dn (Tp T); unfold Dn; omega
  unfold Pool.P0191.xrN
  rw [dif_pos hD0]
  exact occ_hyp0 hn hK

theorem hx_F (hn : 1 ≤ n) (hq : 0 < q) : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QM n T q A).xr i ≤
    max (KcF n T q : ℝ) ((Tp T : ℝ) / (n * (QM n T q A).Bt i)) := fun j _ => by
  have hK := KcF_pos n T q hq
  unfold Pool.P0191.xrN
  split_ifs with h
  · exact occ_hyp hn hK j
  · rw [div_one]; exact le_max_of_le_left (by exact_mod_cast hK)

theorem hxr_F (hq : 0 < q) : ∀ j, Pool.P0282.xf n (Tp T) (KcF n T q) ≤ (QM n T q A).xr j :=
  fun j => floor_le_xr (KcF_pos n T q hq) j

theorem hE_F (i : Fin n) : ∀ j a, j < (QM n T q A).D → (QM n T q A).Bt j ∣ a → a < Tp T →
    (QM n T q A).E (cstarF n T i j a) = a := fun _ _ hj hd ha => cstarF_E n T i hj ha hd

theorem hthr_F (i : Fin n) : ∀ j a, j < (QM n T q A).D → (QM n T q A).Bt j ∣ a → a < Tp T →
    (QM n T q A).thr0 (cstarF n T i j a) = j := fun _ _ hj hd ha => cstarF_thr n T i hj ha hd

theorem harm_F (i : Fin n) : ∀ j a, j < (QM n T q A).D → (QM n T q A).Bt j ∣ a → a < Tp T →
    (QM n T q A).arm (cstarF n T i j a) = i := fun _ _ hj hd ha => cstarF_arm n T i hj ha hd

theorem hTL_F : Tp T ≤ 2 ^ LA T := by unfold Tp LA; exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem hρ_F : ∀ i, 1 ≤ i → ((QM n T q A).Bt (i - 1) : ℝ) ≤ 2 * (QM n T q A).Bt i :=
  fun i hi => Bt_pred_le (Tp T) i hi

theorem hlay_F : (QM n T q A).lay = Pool.P0176.sortLay (QM n T q A).sl := rfl

theorem hT_F : (QM n T q A).Bt 0 ∣ Tp T := by show Bt (Tp T) 0 ∣ Tp T; rw [Bt0_Tp]

theorem h1_F (hq : 0 < q) (hq1 : q ≤ 1 / 32) : 1 ≤ APF n T q A + BPF n T q A := by
  have hK := KcF_pos n T q hq
  have hθ : (1 : ℝ) ≤ (QM n T q A).θ := by
    show (1 : ℝ) ≤ (θc n (Tp T) (Kq q) : ℝ)
    have : 1 ≤ θc n (Tp T) (Kq q) := le_trans hK (le_max_left _ _)
    exact_mod_cast this
  have hα := Pool.P0226.αT_nonneg (ι := CpG n (Tp T)) (η := ηA n T q) (L := LA T) (T := Tp T) (ηA_pos n T q)
    (δ := εA n T q) (by unfold εA; have := ηA_pos n T q; positivity)
  have hLx := (Lx_pos n T).le
  have hη := ηA_pos n T q
  have hw : 0 < wEA n T q A := by have := Pool.P0284.wEA_ge n T q A hq hq1; linarith
  have hxf := xf_pos (n := n) (T' := Tp T) hK
  have hB : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  have hA : 1 ≤ APF n T q A := by
    unfold APF AP
    have h2 : 0 ≤ Lx n T / (2 * (wEA n T q A * ηA n T q)) := div_nonneg hLx (by positivity)
    have h3 : 0 ≤ 2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q) := div_nonneg (by linarith) hxf.le
    have h4 := Real.sqrt_nonneg (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)))
    have h5 : 0 ≤ Lx n T / ηA n T q := div_nonneg hLx hη.le
    have h6 : (0 : ℝ) ≤ (Pool.P0225.withAlgG (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
      (wEA n T q A) (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
        (εA n T q))).R := Nat.cast_nonneg _
    have h7 : (1 : ℝ) ≤ (Pool.P0225.withAlgG (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
      (wEA n T q A) (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
        (εA n T q))).θ := hθ
    have h8 : 0 ≤ (Pool.P0225.withAlgG (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
      (wEA n T q A) (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
        (εA n T q))).R * (2 * Pool.P0226.αT (ι := CpG n (Tp T)) (ηA n T q) (LA T) (Tp T) (εA n T q) +
          2 * (Lx n T / (2 * (wEA n T q A * ηA n T q)))) := by positivity
    have h9 : 0 ≤ ((Pool.P0225.withAlgG (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
      (wEA n T q A) (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
        (εA n T q))).R + 1) * (2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q) +
          2 * Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)))) := by positivity
    linarith
  linarith

theorem hlayOK_F : Pool.P0191.LayOK (QM n T q A).sl (QM n T q A).lay := Pool.P0191.layOK_sort _

theorem hcw_F (hq : 0 < q) : (QM n T q A).cB * (QM n T q A).wB = 1 := by
  show 1 / (q / 2) * (q / 2) = 1; field_simp

theorem hlevT_F : (QM n T q A).lev = Pool.P0085.levTh (Ld (Tp T)) (QM n T q A).Bt := rfl

theorem hLv2_F : Ld (Tp T) + 2 ≤ (QM n T q A).Lv := le_refl _

theorem hEm_F : Monotone (QM n T q A).E := CpG_E_mono n (Tp T)

theorem hTθ_F (hq : 0 < q) : 1 / Pool.P0282.xf n (Tp T) (KcF n T q) * Tp T ≤
    2 ^ ((QM n T q A).R - 1) * (QM n T q A).θ := by
  have hK := KcF_pos n T q hq
  rw [one_div_xf (n := n) (T' := Tp T) hK]
  show ((max (KcF n T q) (Bm n (Tp T)) : ℕ) : ℝ) * Tp T ≤ 2 ^ (Rc (Tp T) - 1) * (θc n (Tp T) (Kq q) : ℝ)
  have e : θc n (Tp T) (Kq q) = max (KcF n T q) (Bm n (Tp T)) := rfl
  rw [e, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast T_le_R (Tp T)

theorem hM0_F : 16 * ((QM n T q A).R : ℝ) ≤ (Pool.P0261.M0 n (Tp T) : ℝ) := Pool.P0261.hM0 n (Tp T)

theorem hk_F : 4 * ((QM n T q A).R : ℝ) * (kk n (Tp T) : ℕ) ≤ (Pool.P0261.M0 n (Tp T) : ℝ) :=
  Pool.P0261.hk n (Tp T)

theorem hp_F : (M0 n T q A).q * (Real.exp 1 - 1) ≤ 1 / (32 * ((QM n T q A).R : ℝ)) := Pool.P0261.hp n (Tp T)

theorem hs_F : ∀ a r : ℕ, a < Tp T → r < (QM n T q A).D →
    ∑ F ∈ (Finset.univ.filter fun c => (QM n T q A).E c = a ∧ (QM n T q A).thr0 c = r).powerset,
      (M0 n T q A).ps ^ F.card * (1 - (M0 n T q A).ps) ^
        ((Finset.univ.filter fun c => (QM n T q A).E c = a ∧ (QM n T q A).thr0 c = r).card - F.card) *
        (if s0 n (Tp T) < F.card then 1 else 0) ≤ Real.exp (Real.exp 1 - 1 - (s0 n (Tp T) + 1)) :=
  Pool.P0261.hs (Tp_pos T)

theorem hρS_F (hn : 1 ≤ n) : (1 - 1 / (4 * (QM n T q A).R : ℝ)) ^ (QM n T q A).K *
    ((Sp n (Tp T) : ℝ) + (s0 n (Tp T) + (QM n T q A).D * (QM n T q A).Lv * Sp n (Tp T))) ≤ Sp n (Tp T) :=
  Pool.P0261.hρS hn (Tp_pos T)

theorem hsl_F : ∀ j, ((QM n T q A).D : ℝ) * ((s0 n (Tp T) + (QM n T q A).D * (QM n T q A).Lv * Sp n (Tp T)) +
    ((QM n T q A).Lv - 1 : ℕ) * Sp n (Tp T)) + (QM n T q A).D * s0 n (Tp T) + 1 ≤ (QM n T q A).sl j :=
  fun _ => Pool.P0261.hsl n (Tp T)

theorem APF_nonneg (hq : 0 < q) (hq1 : q ≤ 1 / 32) : 0 ≤ APF n T q A := by
  have := h1_F n T q A hq hq1
  have hB : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  unfold APF; exact Pool.P0282.AP_nonneg _ _ _ _ _ _ _ _ _ (ηA_pos n T q)
    (by unfold εA; have := ηA_pos n T q; positivity) (ηA_pos n T q)
    (by have := Pool.P0284.wEA_ge n T q A hq hq1; linarith) (Lx_pos n T).le (Lx_pos n T).le (Lx_pos n T).le
    (ηA_pos n T q) (xf_pos (n := n) (T' := Tp T) (KcF_pos n T q hq)) (Nat.cast_nonneg _)

theorem MwF_nonneg (hq : 0 < q) (hq1 : q ≤ 1 / 32) : 0 ≤ MwF n T q A := by
  unfold MwF
  have := APF_nonneg n T q A hq hq1
  have hB : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  positivity

theorem hMa_F (hq : 0 < q) (hq1 : q ≤ 1 / 32) : ∀ j, 1 ≤ j → j < (QM n T q A).D → ¬ czF n T j →
    2 * (APF n T q A + BPF n T q A * √((QM n T q A).Bt j : ℝ)) ≤ MwF n T q A := by
  intro j _ _ hcz
  unfold czF at hcz; push Not at hcz
  have hA := APF_nonneg n T q A hq hq1
  have hB : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hs : √((QM n T q A).Bt j : ℝ) ≤ Real.sqrt ((Tp T : ℝ) / n) := by
    apply Real.sqrt_le_sqrt
    show ((Bt (Tp T) j : ℕ) : ℝ) ≤ (Tp T : ℝ) / n
    rw [le_div_iff₀ hn]
    have : n * Bt (Tp T) j ≤ Tp T := hcz.le
    have : ((n * Bt (Tp T) j : ℕ) : ℝ) ≤ Tp T := by exact_mod_cast this
    push_cast at this; linarith
  unfold MwF
  nlinarith

theorem hMc_F (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) :
    ccP (APF n T q A) (BPF n T q A) (QM n T q A).Bt (QM n T q A).D ≤ MwF n T q A := by
  have hA := APF_nonneg n T q A hq hq1
  have hB : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  have hn' : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have h1 : (1 : ℝ) ≤ Real.sqrt ((Tp T : ℝ) / n) := by
    rw [Real.one_le_sqrt, le_div_iff₀ hn', one_mul]
    exact_mod_cast hnT.trans (le_Tp T)
  unfold ccP MwF
  show APF n T q A + BPF n T q A * √((Bt (Tp T) (Dn (Tp T) - 1) : ℕ) : ℝ) ≤ _
  rw [Pool.P0282.Bt_last]; simp only [Nat.cast_one, Real.sqrt_one, mul_one]
  nlinarith

/-- The overflow closed form of P0185/P0221 at `famM` (P0281's shape). -/
noncomputable abbrev ovfBF : ℝ :=
  (Tp T : ℝ) * (QM n T q A).D * Real.exp (Real.exp 1 - 1 - (s0 n (Tp T) + 1)) + (Tp T : ℝ) * (QM n T q A).D *
    ((M0 n T q A).Lf + 1) * (QM n T q A).K * Pool.P0042.delta (Fintype.card (CpG n (Tp T))) (M0 n T q A).q
      (QM n T q A).R (kk n (Tp T)) (Pool.P0261.M0 n (Tp T))

/-- P0207/P0259's bad-start count at `famM` (P0281's shape). -/
noncomputable abbrev countF : ℝ :=
  ((QM n T q A).D * (QM n T q A).Lv * (s0 n (Tp T) + (QM n T q A).D * (QM n T q A).Lv * Sp n (Tp T) + 1) : ℝ) /
    ((M0 n T q A).ps * (1 - (M0 n T q A).q) ^ ((QM n T q A).K * ((QM n T q A).D *
      (2 * Ld (Tp T) + Tp T / 2 ^ Ld (Tp T) + 1))))

/-- P0259's coarse sum at `famM`. -/
noncomputable abbrev coarseF : ℝ :=
  Pool.P0259.coarseSum (Tp T) (QM n T q A).D (QM n T q A).Bt (czF n T)
    (Pool.P0266.aW (APF n T q A) (BPF n T q A) (QM n T q A).Bt 2)

/-- P0243's per-round budget at `famM`. -/
noncomputable abbrev CbF : ℝ :=
  Pool.P0243.Cb (ηA n T q) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (∑ j : Fin (QM n T q A).D, ((QM n T q A).sl j : ℝ)) (ηA n T q)

/-- The exponential tails at `famM`. -/
noncomputable abbrev tailF : ℝ :=
  2 * (Fintype.card (CpG n (Tp T)) * (2 * ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T))) +
    2 * ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T) +
    Fintype.card (CpG n (Tp T)) * (((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T)) +
    ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T) + ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **P0281's ALG-term bound at P0284's machine**, every hypothesis discharged. -/
theorem algT_famM_raw (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32)
    (ℓ : Pool.P0001.LossSeq n) (rc₀ : RC (famM n T q A).P) (i : Fin n) :
    ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (famM n T q A)) (Tp T) → Bool,
        Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
          Pool.P0217.algT (famM n T q A) (Tp T) ℓ rc₀ i arr ≤
      wEA n T q A * ((Tp T : ℝ) * (APF n T q A / (QM n T q A).Bt 0 + BPF n T q A / √((QM n T q A).Bt 0 : ℝ)) +
          (coarseF n T q A + MwF n T q A * (countF n T q A + (QM n T q A).D * (Tp T : ℝ) * ovfBF n T q A))) +
        wEA n T q A * ((Tp T : ℝ) * CbF n T q A) +
        wEA n T q A * (Tp T : ℝ) * (2 * ovfBF n T q A + tailF n T) +
        (M0 n T q A).P.wE * (Tp T : ℝ) * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
          Pool.P0217.ovf (famM n T q A) (Tp T) ℓ rc₀ arr := by
  have hK := KcF_pos n T q hq
  have hTp := Tp_pos T
  have hD0 : 0 < Dn (Tp T) := by unfold Dn; omega
  have hw := Pool.P0284.wEA_ge n T q A hq hq1
  have hLx := Lx_pos n T
  have hxf := xf_pos (n := n) (T' := Tp T) hK
  have h := Pool.P0281.algT_arr_twin (M0 n T q A) (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
    (wEA n T q A) (Tp T) ℓ (Tp T) rc₀ (Dp (Tp T)) (hΘn_F n T q A) hD0 (hL_F n T q A hq hq1)
    (by show 0 < NA n T q; unfold NA; omega) (ηA_pos n T q)
    (by unfold εA; have := ηA_pos n T q; have : (0 : ℝ) < Tp T := by exact_mod_cast hTp
        positivity)
    (ηA_pos n T q) (by linarith) rfl (hTL_F T) (by show (0 : ℝ) ≤ 1 / (q / 2); positivity)
    (Ls := Lx n T) (Lb := Lx n T) (Lc := Lx n T) (Lt := Lx n T) (κ := ηA n T q)
    (xmin := Pool.P0282.xf n (Tp T) (KcF n T q)) (M := KcF n T q) (ρ := 2) (nn := n) (TT := Tp T) (Θ := Dp (Tp T))
    hLx.le hLx.le hLx.le hLx.le (ηA_pos n T q) hxf (xf_le_one (n := n) (T' := Tp T) hK) (hxr_F n T q A hq)
    (by exact_mod_cast NeZero.pos n) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num)
    (fun i => Nat.two_pow_pos _) (hρ_F n T q A) (hx0_F n T q A hn hq) (hx_F n T q A hn hq) (hΘ_F n T q A)
    (hlay_F n T q A) (Nat.cast_nonneg _) (Rc_pos _) (btHyp (Tp T)) (hT_F n T q A)
    (cstarF n T i) (hE_F n T q A i) (hthr_F n T q A i) i (harm_F n T q A i) (hΛ'_F n T q A)
    (by positivity) (h1_F n T q A hq hq1) (hlayOK_F n T q A) (fun j => xr_pos hK j) (fun j => xr_le_one hK j)
    (hcw_F n T q A hq) hLx hLx (ηA_le_one n T q)
    (Ld := Ld (Tp T)) (hlevT_F n T q A) (hLv2_F n T q A) le_rfl
    (by show (0 : ℝ) < 1 / n; have : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
        positivity)
    (by show (1 : ℝ) / n ≤ 1; rw [div_le_one (by exact_mod_cast NeZero.pos n)]; exact_mod_cast hn)
    (qf_mem n (Tp T)).1 (qf_lt_one n (Tp T)) (hEm_F n T q A)
    (by rw [one_div_xf (n := n) (T' := Tp T) hK]; exact_mod_cast le_trans hK (le_max_left _ _))
    (hTθ_F n T q A hq)
    (Pool.P0261.M0 n (Tp T)) (kk n (Tp T)) (hM0_F n T q A) (hk_F n T q A) (hp_F n T q A)
    (s0 n (Tp T)) (Real.exp (Real.exp 1 - 1 - (s0 n (Tp T) + 1))) (hs_F n T q A)
    (Sp n (Tp T)) (Pool.P0261.hM0S n (Tp T)) (hρS_F n T q A hn) (hsl_F n T q A)
    (by show 1 ≤ NA n T q; unfold NA; omega)
    (MwF n T q A) (MwF_nonneg n T q A hq hq1) (czF n T) (hMa_F n T q A hq hq1) (hMc_F n T q A hn hnT hq hq1)
    le_rfl
  exact h

end Inst

end Pool.P0290
