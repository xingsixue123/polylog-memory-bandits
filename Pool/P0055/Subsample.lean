import Pool.P0012.Potential

/-!
# Flagged runs of a homogeneous machine, and compression

For a machine `A` (we use its round-`0` kernels; for a homogeneous machine these are all its kernels), a loss sequence
`ℓ` and update flags `f : ℕ → Bool`, the **flagged run** updates the state only on flagged rounds:
`X 0 ∼ init`, and `X (t+1)` is one step of `A` with loss vector `ℓ t` if `f t`, else `X t`.

* `cnt f t`: the number of flagged rounds before `t`.
* `compress ℓ f t`: the loss sequence seen by `A` on the flagged rounds before `t`
  (`compress ℓ f t k = ℓ (k-th flagged round)` for `k < cnt f t`).
* `runF_eq_stateDist`: for a homogeneous machine, the flagged run at round `t` has the law of `A`'s ordinary run on
  `compress ℓ f t` at round `cnt f t`.
-/

open scoped ENNReal

namespace Pool.P0055

open Pool.P0001

variable {n : ℕ}

/-- One step of `A` (round-`0` kernels) with loss vector `v`. -/
noncomputable def step0 (A : Machine n) (v : Fin n → Bool) (s : A.State) : PMF A.State :=
  (A.act 0 s).bind fun a => A.next 0 s a (v a)

/-- The flagged run. -/
noncomputable def runF (A : Machine n) (ℓ : LossSeq n) (f : ℕ → Bool) : ℕ → PMF A.State
  | 0 => A.init
  | t + 1 => if f t then (runF A ℓ f t).bind (step0 A (ℓ t)) else runF A ℓ f t

/-- Number of flagged rounds before `t`. -/
def cnt (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 => if f t then cnt f t + 1 else cnt f t

/-- The compressed loss sequence of the flagged rounds before `t`. -/
def compress (ℓ : LossSeq n) (f : ℕ → Bool) : ℕ → LossSeq n
  | 0 => ℓ
  | t + 1 => if f t then (fun k => if k = cnt f t then ℓ t else compress ℓ f t k) else compress ℓ f t

/-- `stateDist` at round `t` only depends on the losses of rounds `< t`. -/
lemma stateDist_congr (A : Machine n) {ℓ ℓ' : LossSeq n} :
    ∀ t, (∀ k, k < t → ℓ k = ℓ' k) → A.stateDist ℓ t = A.stateDist ℓ' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    simp only [Machine.stateDist]
    rw [ih (fun k hk => h k (by omega)), h t (by omega)]

/-- The compressed sequences are prefix-consistent: at `t+1` they agree with those at `t` below `cnt f t`. -/
lemma compress_succ_lt (ℓ : LossSeq n) (f : ℕ → Bool) (t k : ℕ) (hk : k < cnt f t) :
    compress ℓ f (t + 1) k = compress ℓ f t k := by
  have hne : k ≠ cnt f t := by omega
  by_cases h : f t = true
  · simp [compress, h, hne]
  · have hf : f t = false := by simpa using h
    simp [compress, hf]

lemma compress_succ_cnt (ℓ : LossSeq n) (f : ℕ → Bool) (t : ℕ) (h : f t = true) :
    compress ℓ f (t + 1) (cnt f t) = ℓ t := by
  simp [compress, h]

/-- **Compression.** For a homogeneous machine, the flagged run is the ordinary run on the compressed sequence. -/
theorem runF_eq_stateDist (A : Machine n) (hA : A.IsHomogeneous) (ℓ : LossSeq n) (f : ℕ → Bool) :
    ∀ t, runF A ℓ f t = A.stateDist (compress ℓ f t) (cnt f t) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h : f t = true
    · simp only [runF, h, ite_true, cnt]
      rw [ih]
      simp only [Machine.stateDist]
      have hcong : A.stateDist (compress ℓ f t) (cnt f t) = A.stateDist (compress ℓ f (t + 1)) (cnt f t) :=
        stateDist_congr A (cnt f t) (fun k hk => (compress_succ_lt ℓ f t k hk).symm)
      rw [hcong, compress_succ_cnt ℓ f t h]
      congr 1
      funext s
      unfold step0
      congr 1
      · exact (hA.1 (cnt f t) s).symm
      · funext a
        exact (hA.2 (cnt f t) s a _).symm
    · have hf : f t = false := by simpa using h
      simp only [runF, hf, cnt, compress]
      simp only [Bool.false_eq_true, ite_false]
      exact ih

end Pool.P0055

namespace Pool.P0055

open Pool.P0001 Finset
open scoped ENNReal

variable {n : ℕ}

/-! ### Reindexing sums over flagged rounds -/

lemma cnt_mono (f : ℕ → Bool) (t : ℕ) : cnt f t ≤ cnt f (t + 1) := by
  simp only [cnt]; split_ifs <;> omega

lemma cnt_le (f : ℕ → Bool) : ∀ t, cnt f t ≤ t := by
  intro t; induction t with
  | zero => simp [cnt]
  | succ t ih => simp only [cnt]; split_ifs <;> omega

/-- `Σ_{t<T} 1[f t] h(cnt f t) = Σ_{k < cnt f T} h k`. -/
lemma sum_flag_reindex (f : ℕ → Bool) (h : ℕ → ℝ) :
    ∀ T, ∑ t ∈ range T, (if f t then h (cnt f t) else 0) = ∑ k ∈ range (cnt f T), h k := by
  intro T
  induction T with
  | zero => simp [cnt]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hf : f T = true
    · simp [cnt, hf, Finset.sum_range_succ]
    · have : f T = false := by simpa using hf
      simp [cnt, this]

lemma cnt_mono_add (f : ℕ → Bool) (t : ℕ) : ∀ d, cnt f t ≤ cnt f (t + d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih => exact ih.trans (by rw [← add_assoc]; exact cnt_mono f (t + d))

lemma cnt_mono' (f : ℕ → Bool) {t T : ℕ} (h : t ≤ T) : cnt f t ≤ cnt f T := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact cnt_mono_add f t d

/-- The compressed sequence at the horizon keeps the value assigned when a flagged round was processed. -/
lemma compress_stable_add (ℓ : LossSeq n) (f : ℕ → Bool) (t k : ℕ) (hk : k < cnt f t) :
    ∀ d, compress ℓ f (t + d) k = compress ℓ f t k := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, compress_succ_lt ℓ f (t + d) k (lt_of_lt_of_le hk (cnt_mono_add f t d)), ih]

lemma compress_stable (ℓ : LossSeq n) (f : ℕ → Bool) (t k : ℕ) (hk : k < cnt f t) (T : ℕ) (hT : t ≤ T) :
    compress ℓ f T k = compress ℓ f t k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hT
  exact compress_stable_add ℓ f t k hk d

lemma compress_at_flag (ℓ : LossSeq n) (f : ℕ → Bool) (t T : ℕ) (htT : t < T) (hf : f t = true) :
    compress ℓ f T (cnt f t) = ℓ t := by
  have h1 : cnt f t < cnt f (t + 1) := by simp [cnt, hf]
  rw [compress_stable ℓ f (t + 1) (cnt f t) h1 T htT, compress_succ_cnt ℓ f t hf]

end Pool.P0055

namespace Pool.P0055

open Pool.P0001 Finset
open scoped ENNReal

variable {n : ℕ}

/-! ### Flag tuples, product weights, and the subsampled machine -/

/-- Product weight of a flag tuple: `γ` per `true`, `1 - γ` per `false`. -/
def wt (γ : ℝ) {t : ℕ} (F : Fin t → Bool) : ℝ := ∏ i, (if F i then γ else 1 - γ)

/-- Extension of a flag tuple by `false`. -/
def ext {t : ℕ} (F : Fin t → Bool) : ℕ → Bool := fun k => if h : k < t then F ⟨k, h⟩ else false

lemma runF_congr (A : Machine n) (ℓ : LossSeq n) {f g : ℕ → Bool} :
    ∀ t, (∀ k, k < t → f k = g k) → runF A ℓ f t = runF A ℓ g t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    simp only [runF]
    rw [ih (fun k hk => h k (by omega)), h t (by omega)]

lemma ext_snoc_lt {t : ℕ} (F : Fin t → Bool) (b : Bool) (k : ℕ) (hk : k < t) :
    ext (Fin.snoc F b : Fin (t + 1) → Bool) k = ext F k := by
  have hk' : k < t + 1 := by omega
  simp only [ext, hk, hk', dif_pos]
  have : (⟨k, hk'⟩ : Fin (t + 1)) = Fin.castSucc ⟨k, hk⟩ := rfl
  rw [this, Fin.snoc_castSucc]

lemma ext_snoc_last {t : ℕ} (F : Fin t → Bool) (b : Bool) :
    ext (Fin.snoc F b : Fin (t + 1) → Bool) t = b := by
  have : (⟨t, by omega⟩ : Fin (t + 1)) = Fin.last t := rfl
  simp only [ext, show t < t + 1 by omega, dif_pos, this, Fin.snoc_last]

lemma wt_snoc (γ : ℝ) {t : ℕ} (F : Fin t → Bool) (b : Bool) :
    wt γ (Fin.snoc F b : Fin (t + 1) → Bool) = wt γ F * (if b then γ else 1 - γ) := by
  simp [wt, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- Sum over `Fin (t+1) → Bool` as a sum over the last flag and the first `t` flags. -/
lemma sum_fin_succ_bool {t : ℕ} (g : (Fin (t + 1) → Bool) → ℝ) :
    ∑ F, g F = ∑ F' : Fin t → Bool, (g (Fin.snoc F' true) + g (Fin.snoc F' false)) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (t + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.snocEquiv_apply, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]

/-- The `γ`-coin on `Bool`. -/
noncomputable def coin (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then γ else 1 - γ)) (by
    rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add h0 (by linarith)]; simp)

lemma coin_toReal (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (b : Bool) :
    (coin γ h0 h1 b).toReal = if b then γ else 1 - γ := by
  simp only [coin, PMF.ofFintype_apply]
  rw [ENNReal.toReal_ofReal]
  split_ifs <;> linarith

/-- **Subsampled play.** The machine plays `A`'s (round-`0`) policy on every round, but updates `A`'s state only with
probability `γ` (fresh coin each round), using the observed loss of the pulled arm. Same state type as `A`. -/
@[reducible] noncomputable def Sub (A : Machine n) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) : Machine n where
  State := A.State
  fintypeState := A.fintypeState
  init := A.init
  act _ s := A.act 0 s
  next _ s a b := (coin γ h0 h1).bind fun c => if c then A.next 0 s a b else PMF.pure s

end Pool.P0055

namespace Pool.P0055

open Pool.P0001 Finset
open scoped ENNReal

variable {n : ℕ}

lemma sum_toReal_pmf {α : Type} [Fintype α] (μ : PMF α) : ∑ a, (μ a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ a),
    ← tsum_fintype (L := .unconditional _) (fun a => μ a), PMF.tsum_coe, ENNReal.toReal_one]

/-- The transition kernel of the subsampled machine at round `t`. -/
noncomputable def subK (A : Machine n) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (v : Fin n → Bool) (s : A.State) :
    PMF A.State :=
  (A.act 0 s).bind fun a => (coin γ h0 h1).bind fun c => if c then A.next 0 s a (v a) else PMF.pure s

lemma Sub_stateDist_zero (A : Machine n) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ℓ : LossSeq n) :
    ((Sub A γ h0 h1).stateDist ℓ 0 : PMF A.State) = A.init := rfl

lemma Sub_stateDist_succ (A : Machine n) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ℓ : LossSeq n) (t : ℕ) :
    ((Sub A γ h0 h1).stateDist ℓ (t + 1) : PMF A.State) =
      ((Sub A γ h0 h1).stateDist ℓ t : PMF A.State).bind (subK A γ h0 h1 (ℓ t)) := rfl

/-- One step of the subsampled machine, in real numbers. -/
lemma subK_toReal (A : Machine n) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (v : Fin n → Bool) (s s' : A.State) :
    ((subK A γ h0 h1 v s) s').toReal =
      γ * ((step0 A v s) s').toReal + (1 - γ) * ((PMF.pure s : PMF A.State) s').toReal := by
  unfold subK step0
  rw [Pool.P0012.bind_toReal, Pool.P0012.bind_toReal]
  have hin : ∀ a, (((coin γ h0 h1).bind fun c => if c then A.next 0 s a (v a) else PMF.pure s) s').toReal =
      γ * (A.next 0 s a (v a) s').toReal + (1 - γ) * ((PMF.pure s : PMF A.State) s').toReal := by
    intro a
    rw [Pool.P0012.bind_toReal, Fintype.sum_bool, coin_toReal, coin_toReal]
    simp only [ite_true, Bool.false_eq_true, ite_false]
  simp only [hin, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
  · rw [← Finset.sum_mul, sum_toReal_pmf, one_mul]

/-- `Σ_s μ(s)·δ_s(s') = μ(s')`. -/
lemma sum_mul_pure_toReal {α : Type} [Fintype α] (μ : PMF α) (s' : α) :
    ∑ s, (μ s).toReal * ((PMF.pure s : PMF α) s').toReal = (μ s').toReal := by
  rw [← Pool.P0012.bind_toReal, PMF.bind_pure]

/-- **Mixture identity.** The state law of the subsampled machine is the product-weighted mixture of flagged runs. -/
theorem stateDist_Sub_toReal (A : Machine n) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ℓ : LossSeq n) :
    ∀ t (s : A.State), (((Sub A γ h0 h1).stateDist ℓ t : PMF A.State) s).toReal =
      ∑ F : Fin t → Bool, wt γ F * ((runF A ℓ (ext F) t) s).toReal := by
  intro t
  induction t with
  | zero =>
    intro s
    rw [Sub_stateDist_zero]
    simp [wt, runF]
  | succ t ih =>
    intro s'
    rw [Sub_stateDist_succ, Pool.P0012.bind_toReal]
    simp only [subK_toReal, mul_add, Finset.sum_add_distrib]
    rw [sum_fin_succ_bool]
    have hR : ∀ F' : Fin t → Bool,
        wt γ (Fin.snoc F' true : Fin (t + 1) → Bool) *
            ((runF A ℓ (ext (Fin.snoc F' true : Fin (t + 1) → Bool)) (t + 1)) s').toReal +
          wt γ (Fin.snoc F' false : Fin (t + 1) → Bool) *
            ((runF A ℓ (ext (Fin.snoc F' false : Fin (t + 1) → Bool)) (t + 1)) s').toReal =
        γ * ∑ s, (wt γ F' * ((runF A ℓ (ext F') t) s).toReal) * ((step0 A (ℓ t) s) s').toReal +
          (1 - γ) * ∑ s, (wt γ F' * ((runF A ℓ (ext F') t) s).toReal) *
            ((PMF.pure s : PMF A.State) s').toReal := by
      intro F'
      have hc : ∀ b : Bool, runF A ℓ (ext (Fin.snoc F' b : Fin (t + 1) → Bool)) t = runF A ℓ (ext F') t :=
        fun b => runF_congr A ℓ t (fun k hk => ext_snoc_lt F' b k hk)
      simp only [runF, ext_snoc_last, ite_true, Bool.false_eq_true, ite_false, hc, wt_snoc]
      rw [Pool.P0012.bind_toReal]
      have hp : ∑ s, (wt γ F' * ((runF A ℓ (ext F') t) s).toReal) * ((PMF.pure s : PMF A.State) s').toReal =
          wt γ F' * ((runF A ℓ (ext F') t) s').toReal := by
        simp only [mul_assoc]; rw [← Finset.mul_sum, sum_mul_pure_toReal]
      rw [hp, Finset.mul_sum]
      rw [Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · ring
    rw [Finset.sum_congr rfl fun F' _ => hR F', Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_comm (f := fun F' s => (wt γ F' * ((runF A ℓ (ext F') t) s).toReal) *
        ((step0 A (ℓ t) s) s').toReal)]
    rw [Finset.sum_comm (f := fun F' s => (wt γ F' * ((runF A ℓ (ext F') t) s).toReal) *
        ((PMF.pure s : PMF A.State) s').toReal)]
    simp only [← Finset.sum_mul, ← ih]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => by ring
    · refine Finset.sum_congr rfl fun s _ => by ring

end Pool.P0055

namespace Pool.P0055

open Pool.P0001 Finset
open scoped ENNReal

variable {n : ℕ}

/-! ### Marginalization over product weights -/

/-- Restriction of a flag tuple to its first `t` coordinates. -/
def restr {t T : ℕ} (h : t ≤ T) (F : Fin T → Bool) : Fin t → Bool := fun i => F ⟨i.1, by omega⟩

lemma restr_snoc {t T : ℕ} (h : t ≤ T) (F : Fin T → Bool) (b : Bool) :
    restr (by omega : t ≤ T + 1) (Fin.snoc F b : Fin (T + 1) → Bool) = restr h F := by
  funext i
  simp only [restr]
  have : (⟨i.1, by omega⟩ : Fin (T + 1)) = Fin.castSucc ⟨i.1, by omega⟩ := rfl
  rw [this, Fin.snoc_castSucc]

lemma restr_self {t : ℕ} (F : Fin t → Bool) : restr le_rfl F = F := by
  funext i; rfl

/-- Summing out the flags after `t`: total weight one. -/
lemma sum_wt_restr (γ : ℝ) (t : ℕ) (Φ : (Fin t → Bool) → ℝ) :
    ∀ d, ∑ F : Fin (t + d) → Bool, wt γ F * Φ (restr (by omega) F) = ∑ F' : Fin t → Bool, wt γ F' * Φ F' := by
  intro d
  induction d with
  | zero => simp [restr_self]
  | succ d ih =>
    have e : t + (d + 1) = (t + d) + 1 := by omega
    rw [show (∑ F : Fin (t + (d + 1)) → Bool, wt γ F * Φ (restr (by omega) F)) =
        ∑ F : Fin ((t + d) + 1) → Bool, wt γ F * Φ (restr (by omega) F) from rfl]
    rw [sum_fin_succ_bool]
    simp only [wt_snoc, restr_snoc (by omega : t ≤ t + d), ite_true, Bool.false_eq_true, ite_false]
    rw [← ih]
    refine Finset.sum_congr rfl fun F _ => by ring

/-- Conditioning on the flag of round `t`: weight `γ`. -/
lemma sum_wt_flag_restr (γ : ℝ) (t : ℕ) (Φ : (Fin t → Bool) → ℝ) :
    ∀ d, ∑ F : Fin (t + 1 + d) → Bool,
        wt γ F * ((if F ⟨t, by omega⟩ then 1 else 0) * Φ (restr (by omega) F)) =
      γ * ∑ F' : Fin t → Bool, wt γ F' * Φ F' := by
  intro d
  induction d with
  | zero =>
    rw [show (∑ F : Fin (t + 1 + 0) → Bool, wt γ F * ((if F ⟨t, by omega⟩ then 1 else 0) * Φ (restr (by omega) F))) =
        ∑ F : Fin (t + 1) → Bool, wt γ F * ((if F ⟨t, by omega⟩ then 1 else 0) * Φ (restr (by omega) F)) from rfl]
    rw [sum_fin_succ_bool]
    have hl : ∀ (F' : Fin t → Bool) (b : Bool), (Fin.snoc F' b : Fin (t + 1) → Bool) ⟨t, by omega⟩ = b := by
      intro F' b
      have : (⟨t, by omega⟩ : Fin (t + 1)) = Fin.last t := rfl
      rw [this, Fin.snoc_last]
    simp only [wt_snoc, hl, restr_snoc le_rfl, restr_self, ite_true, Bool.false_eq_true, ite_false]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ => by ring
  | succ d ih =>
    rw [show (∑ F : Fin (t + 1 + (d + 1)) → Bool,
          wt γ F * ((if F ⟨t, by omega⟩ then 1 else 0) * Φ (restr (by omega) F))) =
        ∑ F : Fin ((t + 1 + d) + 1) → Bool,
          wt γ F * ((if F ⟨t, by omega⟩ then 1 else 0) * Φ (restr (by omega) F)) from rfl]
    rw [sum_fin_succ_bool]
    have hl : ∀ (F' : Fin (t + 1 + d) → Bool) (b : Bool),
        (Fin.snoc F' b : Fin (t + 1 + d + 1) → Bool) ⟨t, by omega⟩ = F' ⟨t, by omega⟩ := by
      intro F' b
      have : (⟨t, by omega⟩ : Fin (t + 1 + d + 1)) = Fin.castSucc ⟨t, by omega⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    simp only [wt_snoc, hl, restr_snoc (by omega : t ≤ t + 1 + d), ite_true, Bool.false_eq_true, ite_false]
    rw [← ih]
    refine Finset.sum_congr rfl fun F _ => by ring

end Pool.P0055

namespace Pool.P0055

open Pool.P0001 Finset
open scoped ENNReal

variable {n : ℕ}

lemma wt_nonneg {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) {t : ℕ} (F : Fin t → Bool) : 0 ≤ wt γ F :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> linarith

lemma sum_wt (γ : ℝ) : ∀ t, ∑ F : Fin t → Bool, wt γ F = 1 := by
  intro t
  induction t with
  | zero => simp [wt]
  | succ t ih =>
    rw [sum_fin_succ_bool]
    simp only [wt_snoc, ite_true, Bool.false_eq_true, ite_false]
    calc ∑ F : Fin t → Bool, (wt γ F * γ + wt γ F * (1 - γ)) = ∑ F : Fin t → Bool, wt γ F :=
          Finset.sum_congr rfl fun F _ => by ring
      _ = 1 := ih

/-- Marginalization at a general horizon `T > t`. -/
lemma sum_wt_flag (γ : ℝ) {t T : ℕ} (ht : t < T) (Φ : (Fin t → Bool) → ℝ) :
    ∑ F : Fin T → Bool, wt γ F * ((if F ⟨t, ht⟩ then 1 else 0) * Φ (restr ht.le F)) =
      γ * ∑ F' : Fin t → Bool, wt γ F' * Φ F' := by
  obtain ⟨d, rfl⟩ : ∃ d, T = t + 1 + d := ⟨T - t - 1, by omega⟩
  exact sum_wt_flag_restr γ t Φ d

lemma ext_restr {t T : ℕ} (h : t ≤ T) (F : Fin T → Bool) (k : ℕ) (hk : k < t) :
    ext (restr h F) k = ext F k := by
  simp [ext, restr, hk, show k < T by omega]

/-- Policy loss at a state: `g t s = Σ_a act(a)·ℓ_t(a)`. -/
noncomputable def gl (A : Machine n) (ℓ : LossSeq n) (t : ℕ) (s : A.State) : ℝ :=
  ∑ a, (A.act 0 s a).toReal * ((ℓ t a).toNat : ℝ)

lemma expLoss_eq_sum (M : Machine n) (ℓ : LossSeq n) (t : ℕ) :
    M.expLoss ℓ t = ∑ s, ((M.stateDist ℓ t) s).toReal * ∑ a, (M.act t s a).toReal * ((ℓ t a).toNat : ℝ) := by
  unfold Machine.expLoss Machine.armDist
  simp only [Pool.P0012.bind_toReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => by ring

/-- Expected loss of the subsampled machine at round `t`, as a mixture over flag tuples. -/
lemma expLoss_Sub (A : Machine n) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ℓ : LossSeq n) (t : ℕ) :
    (Sub A γ h0 h1).expLoss ℓ t =
      ∑ F : Fin t → Bool, wt γ F * ∑ s, ((runF A ℓ (ext F) t) s).toReal * gl A ℓ t s := by
  rw [expLoss_eq_sum]
  change ∑ s : A.State, (((Sub A γ h0 h1).stateDist ℓ t : PMF A.State) s).toReal * gl A ℓ t s = _
  calc ∑ s : A.State, (((Sub A γ h0 h1).stateDist ℓ t : PMF A.State) s).toReal * gl A ℓ t s
      = ∑ s : A.State, (∑ F : Fin t → Bool, wt γ F * ((runF A ℓ (ext F) t) s).toReal) * gl A ℓ t s :=
        Finset.sum_congr rfl fun s _ => by rw [stateDist_Sub_toReal A γ h0 h1 ℓ t s]
    _ = ∑ F : Fin t → Bool, wt γ F * ∑ s, ((runF A ℓ (ext F) t) s).toReal * gl A ℓ t s := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun s _ => by ring

/-- For a flagged round, the flagged run's policy loss is `A`'s expected loss on the compressed sequence. -/
lemma flagged_round_eq (A : Machine n) (hA : A.IsHomogeneous) (ℓ : LossSeq n) (f : ℕ → Bool) (t T : ℕ)
    (htT : t < T) (hf : f t = true) :
    ∑ s, ((runF A ℓ f t) s).toReal * gl A ℓ t s = A.expLoss (compress ℓ f T) (cnt f t) := by
  rw [expLoss_eq_sum, runF_eq_stateDist A hA]
  have hcong : A.stateDist (compress ℓ f t) (cnt f t) = A.stateDist (compress ℓ f T) (cnt f t) :=
    stateDist_congr A (cnt f t) (fun k hk => (compress_stable ℓ f t k hk T htT.le).symm)
  rw [hcong]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  unfold gl
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hA.1 (cnt f t) s, compress_at_flag ℓ f t T htT hf]

end Pool.P0055

namespace Pool.P0055

open Pool.P0001 Finset
open scoped ENNReal

variable {n : ℕ}

/-- Per flag tuple: the loss of `A` on its learning rounds is at most the loss of any fixed arm on those rounds plus
`A`'s regret bound at the number of learning rounds. -/
lemma per_flag_bound (A : Machine n) (hA : A.IsHomogeneous) (ℓ : LossSeq n) (T : ℕ) (R : ℕ → ℝ)
    (hR : ∀ (ℓ' : LossSeq n) m, m ≤ T → regret A ℓ' m ≤ R m) (f : ℕ → Bool) (i : Fin n) :
    ∑ t ∈ range T, (if f t then ∑ s, ((runF A ℓ f t) s).toReal * gl A ℓ t s else 0) ≤
      ∑ t ∈ range T, (if f t then ((ℓ t i).toNat : ℝ) else 0) + R (cnt f T) := by
  set C := compress ℓ f T
  have h1 : ∑ t ∈ range T, (if f t then ∑ s, ((runF A ℓ f t) s).toReal * gl A ℓ t s else 0) =
      ∑ t ∈ range T, (if f t then A.expLoss C (cnt f t) else 0) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    by_cases hf : f t = true
    · rw [if_pos hf, if_pos hf, flagged_round_eq A hA ℓ f t T (Finset.mem_range.1 ht) hf]
    · simp [hf]
  have h2 : ∑ t ∈ range T, (if f t then ((ℓ t i).toNat : ℝ) else 0) =
      ∑ t ∈ range T, (if f t then ((C (cnt f t) i).toNat : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    by_cases hf : f t = true
    · rw [if_pos hf, if_pos hf, show C (cnt f t) = ℓ t from compress_at_flag ℓ f t T (Finset.mem_range.1 ht) hf]
    · simp [hf]
  rw [h1, h2, sum_flag_reindex f (fun k => A.expLoss C k),
    sum_flag_reindex f (fun k => ((C k i).toNat : ℝ))]
  have hreg := hR C (cnt f T) (cnt_le f T)
  have hbest := bestLoss_le_cumLoss C (cnt f T) i
  unfold regret at hreg
  unfold cumLoss at hbest
  linarith

/-- **Subsampled play: regret bound.** For a homogeneous machine `A` whose regret on every loss sequence of length
`m ≤ T` is at most `R m`, the subsampled machine `Sub A γ` (play `A`'s policy every round, update `A` with
probability `γ`) has regret at most `(1/γ)·E[R(#learning rounds)]`, where the number of learning rounds is
`Binomial(T, γ)`. -/
theorem regret_Sub_le [NeZero n] (A : Machine n) (hA : A.IsHomogeneous) {γ : ℝ} (hγ : 0 < γ) (h1 : γ ≤ 1)
    (ℓ : LossSeq n) (T : ℕ) (R : ℕ → ℝ) (hR : ∀ (ℓ' : LossSeq n) m, m ≤ T → regret A ℓ' m ≤ R m) :
    regret (Sub A γ hγ.le h1) ℓ T ≤ (1 / γ) * ∑ F : Fin T → Bool, wt γ F * R (cnt (ext F) T) := by
  obtain ⟨i, hi⟩ := exists_bestLoss_eq ℓ T
  set G : ℕ → (ℕ → Bool) → ℝ := fun t f => ∑ s, ((runF A ℓ f t) s).toReal * gl A ℓ t s with hG
  -- each round of the subsampled machine, as a marginal over full flag tuples
  have hround : ∀ t ∈ range T, (Sub A γ hγ.le h1).expLoss ℓ t =
      (1 / γ) * ∑ F : Fin T → Bool, wt γ F * (if ext F t then G t (ext F) else 0) := by
    intro t ht
    have htT : t < T := Finset.mem_range.1 ht
    rw [expLoss_Sub]
    have hm := sum_wt_flag γ htT (fun F' => G t (ext F'))
    have hcong : ∀ F : Fin T → Bool, G t (ext (restr htT.le F)) = G t (ext F) := by
      intro F
      simp only [hG]
      rw [runF_congr A ℓ t (fun k hk => ext_restr htT.le F k hk)]
    have hflag : ∀ F : Fin T → Bool, ext F t = F ⟨t, htT⟩ := by intro F; simp [ext, htT]
    have hm' : ∑ F : Fin T → Bool, wt γ F * (if ext F t then G t (ext F) else 0) =
        γ * ∑ F' : Fin t → Bool, wt γ F' * G t (ext F') := by
      rw [← hm]
      refine Finset.sum_congr rfl fun F _ => ?_
      rw [hcong F, hflag F]
      split_ifs <;> ring
    rw [hm']
    field_simp
    rfl
  -- the comparator, as a marginal
  have hcomp : ∀ t ∈ range T, ((ℓ t i).toNat : ℝ) =
      (1 / γ) * ∑ F : Fin T → Bool, wt γ F * (if ext F t then ((ℓ t i).toNat : ℝ) else 0) := by
    intro t ht
    have htT : t < T := Finset.mem_range.1 ht
    have hm := sum_wt_flag γ htT (fun _ => ((ℓ t i).toNat : ℝ))
    have hflag : ∀ F : Fin T → Bool, ext F t = F ⟨t, htT⟩ := by intro F; simp [ext, htT]
    have : ∑ F : Fin T → Bool, wt γ F * (if ext F t then ((ℓ t i).toNat : ℝ) else 0) =
        γ * ((ℓ t i).toNat : ℝ) := by
      rw [show γ * ((ℓ t i).toNat : ℝ) = γ * ∑ F' : Fin t → Bool, wt γ F' * ((ℓ t i).toNat : ℝ) by
        rw [← Finset.sum_mul, sum_wt, one_mul], ← hm]
      refine Finset.sum_congr rfl fun F _ => ?_
      rw [hflag F]; split_ifs <;> ring
    rw [this]; field_simp
  have hL : ∑ t ∈ range T, (Sub A γ hγ.le h1).expLoss ℓ t =
      (1 / γ) * ∑ F : Fin T → Bool, wt γ F * ∑ t ∈ range T, (if ext F t then G t (ext F) else 0) := by
    rw [Finset.sum_congr rfl hround, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun F _ => by rw [Finset.mul_sum]
  have hC : cumLoss ℓ T i =
      (1 / γ) * ∑ F : Fin T → Bool, wt γ F * ∑ t ∈ range T, (if ext F t then ((ℓ t i).toNat : ℝ) else 0) := by
    unfold cumLoss
    rw [Finset.sum_congr rfl hcomp, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun F _ => by rw [Finset.mul_sum]
  have hle : ∑ F : Fin T → Bool, wt γ F * ∑ t ∈ range T, (if ext F t then G t (ext F) else 0) ≤
      ∑ F : Fin T → Bool, wt γ F * ∑ t ∈ range T, (if ext F t then ((ℓ t i).toNat : ℝ) else 0) +
        ∑ F : Fin T → Bool, wt γ F * R (cnt (ext F) T) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun F _ => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (per_flag_bound A hA ℓ T R hR (ext F) i) (wt_nonneg hγ.le h1 F)
  unfold regret
  rw [hi, hL, hC]
  have hγinv : 0 ≤ 1 / γ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hle hγinv]

end Pool.P0055

namespace Pool.P0055

open Pool.P0001 Finset
open scoped ENNReal

variable {n : ℕ}

lemma cnt_eq_sum (f : ℕ → Bool) : ∀ T, (cnt f T : ℝ) = ∑ t ∈ range T, (if f t then (1 : ℝ) else 0) := by
  intro T
  induction T with
  | zero => simp [cnt]
  | succ T ih =>
    rw [Finset.sum_range_succ, ← ih]
    by_cases h : f T = true <;> simp [cnt, h]

/-- The expected number of learning rounds is `γ T`. -/
lemma sum_wt_cnt (γ : ℝ) (T : ℕ) : ∑ F : Fin T → Bool, wt γ F * (cnt (ext F) T : ℝ) = γ * T := by
  simp only [cnt_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ t ∈ range T, ∑ F : Fin T → Bool, wt γ F * (if ext F t then (1 : ℝ) else 0) = γ := by
    intro t ht
    have htT : t < T := Finset.mem_range.1 ht
    have hm := sum_wt_flag γ htT (fun _ => (1 : ℝ))
    calc ∑ F : Fin T → Bool, wt γ F * (if ext F t then (1 : ℝ) else 0)
        = ∑ F : Fin T → Bool, wt γ F * ((if F ⟨t, htT⟩ then 1 else 0) * (fun _ => (1 : ℝ)) (restr htT.le F)) := by
          refine Finset.sum_congr rfl fun F _ => ?_
          have : ext F t = F ⟨t, htT⟩ := by simp [ext, htT]
          rw [this]; split_ifs <;> ring
      _ = γ * ∑ F' : Fin t → Bool, wt γ F' * 1 := hm
      _ = γ := by simp [sum_wt]
  rw [Finset.sum_congr rfl this]
  simp; ring

/-- **Square-root corollary.** If `A` has regret at most `c √m` on every loss sequence of every length `m ≤ T`, the
subsampled machine has regret at most `c √(T/γ)`. -/
theorem regret_Sub_le_sqrt [NeZero n] (A : Machine n) (hA : A.IsHomogeneous) {γ : ℝ} (hγ : 0 < γ) (h1 : γ ≤ 1)
    (ℓ : LossSeq n) (T : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hR : ∀ (ℓ' : LossSeq n) m, m ≤ T → regret A ℓ' m ≤ c * Real.sqrt m) :
    regret (Sub A γ hγ.le h1) ℓ T ≤ c * Real.sqrt (T / γ) := by
  have h := regret_Sub_le A hA hγ h1 ℓ T (fun m => c * Real.sqrt m) hR
  -- Cauchy–Schwarz: Σ wt √cnt ≤ √(Σ wt) √(Σ wt cnt) = √(γ T)
  have hw : ∀ F : Fin T → Bool, 0 ≤ wt γ F := fun F => wt_nonneg hγ.le h1 F
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin T → Bool))
    (fun F => Real.sqrt (wt γ F)) (fun F => Real.sqrt (wt γ F) * Real.sqrt (cnt (ext F) T))
  have e1 : ∀ F : Fin T → Bool, Real.sqrt (wt γ F) * (Real.sqrt (wt γ F) * Real.sqrt (cnt (ext F) T)) =
      wt γ F * Real.sqrt (cnt (ext F) T) := by
    intro F; rw [← mul_assoc, Real.mul_self_sqrt (hw F)]
  have e2 : ∀ F : Fin T → Bool, Real.sqrt (wt γ F) ^ 2 = wt γ F := fun F => Real.sq_sqrt (hw F)
  have e3 : ∀ F : Fin T → Bool, (Real.sqrt (wt γ F) * Real.sqrt (cnt (ext F) T)) ^ 2 =
      wt γ F * (cnt (ext F) T : ℝ) := by
    intro F; rw [mul_pow, Real.sq_sqrt (hw F), Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [e1, e2, e3, sum_wt, one_mul, sum_wt_cnt] at hcs
  have hS : ∑ F : Fin T → Bool, wt γ F * Real.sqrt (cnt (ext F) T) ≤ Real.sqrt (γ * T) := by
    apply Real.le_sqrt_of_sq_le
    exact hcs
  have hsum : ∑ F : Fin T → Bool, wt γ F * (c * Real.sqrt (cnt (ext F) T)) =
      c * ∑ F : Fin T → Bool, wt γ F * Real.sqrt (cnt (ext F) T) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun F _ => by ring
  rw [hsum] at h
  calc regret (Sub A γ hγ.le h1) ℓ T ≤ 1 / γ * (c * ∑ F : Fin T → Bool, wt γ F * Real.sqrt (cnt (ext F) T)) := h
    _ ≤ 1 / γ * (c * Real.sqrt (γ * T)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hc) (by positivity)
    _ = c * Real.sqrt (T / γ) := by
        have hγs : Real.sqrt γ ≠ 0 := (Real.sqrt_pos.2 hγ).ne'
        rw [Real.sqrt_mul hγ.le, Real.sqrt_div' _ hγ.le]
        field_simp
        rw [Real.sq_sqrt hγ.le]
        ring

end Pool.P0055
