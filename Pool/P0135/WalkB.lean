import Pool.P0057.Walk

/-!
# The inheritance walk with (b′)-ends at arbitrary rounds and finest continuous arrivals (P0131 §3, O1)

P0057's walk handles comparator copies whose records end at merges. The one-query designs of P0117/P0127/P0131
also end records by rule (b′) at **arbitrary rounds**, and resynchronise with copies entering the finest thread
mid-unit (P0127 §2). This file is the walk with those outcomes, abstractly.

* Outcomes (`Pool.P0135.Out`): `cov e` (covered at a merge `e`), `bev e j` ((b′)-ended at round `e`, while in thread `j`),
  `bad`. `t τ r` is the outcome of the copy entering level `r` at the boundary `τ`; `g u` the outcome of the finest
  continuous copy entering at round `u`.
* `Pool.P0135.walkB`: at a grid point it is P0057's walk (cover: record and jump; bad: descend, finest: record one epoch);
  a (b′)-end is recorded and the walk continues at its end; off the finest grid (`Pos.free`) it uses `g`
  (a bad free copy pays one round).
* `Pool.P0135.HypB`: P0057's hypotheses for covered grid copies, plus: a (b′)-ended copy has `τ < e ≤ T`, thread `j ≤ r`
  and crosses no boundary of a level `< j` in `(τ, e]`; a free covered copy ends at a finest boundary and is aligned;
  a free (b′)-ended copy crosses no boundary of a level `< j`.
* **`Pool.P0135.theWalkB_spec`**: the records tile `[0, T)`; each satisfies `RecOKB` (it matches its outcome; and a
  counted record, i.e. a covered or a finest-bad one, shorter than `B j` lies in a level-`j` epoch that starts bad or
  contains an earlier (b′)-end of the walk with thread `≤ j`); and the counted records shorter than `B j` have total
  length `≤ B j · (nBadB j + #(b′)-records of thread ≤ j)` (P0057's Lemma 4.18 form, with the (b′)-ends as extra
  "bad" epochs, to be paid by their bank).

Not here: the cost assembly `Σ √|I|` (a follow-up), any process satisfying `HypB` (the mid-unit alignment of
P0131 §3 for an actual threaded process), any certificate or probability.
-/

namespace Pool.P0135

open Pool.P0057

/-- Outcome of a comparator copy: covered at a merge `e`, (b′)-ended at round `e`, or bad. In `bev e j` the thread
`j` is the copy's thread **after** the inheritance at `e` (P0131's convention `curT(c, e)`): if `e` is itself a
boundary of a coarser level, `j` already includes that move. With `HypB.bnc`/`HypB.fbnc` (`m ≤ e` inclusive) this
is the only consistent reading. -/
inductive Out where
  | cov (e : ℕ)
  | bev (e j : ℕ)
  | bad
  deriving DecidableEq

structure RecB where
  start : ℕ
  stop : ℕ
  lvl : ℕ
  free : Bool
  out : Out

/-- Walk positions: a grid point `u` at level `ℓ`, or a round `u` off the finest grid. -/
inductive Pos where
  | grid (u ℓ : ℕ)
  | free (u : ℕ)

variable (R T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Out) (g : ℕ → Out)

/-- Where the walk continues after a record ending at `e`. -/
noncomputable def next (e : ℕ) : Pos :=
  if B (R - 1) ∣ e then .grid e (canon R B e) else .free e

/-- The walk with fuel. -/
noncomputable def walkB : ℕ → Pos → List RecB
  | 0, _ => []
  | f + 1, .grid u ℓ =>
    if T ≤ u then [] else
    match t u ℓ with
    | .cov e => ⟨u, e, ℓ, false, .cov e⟩ :: walkB f (next R B e)
    | .bev e j => ⟨u, e, ℓ, false, .bev e j⟩ :: walkB f (next R B e)
    | .bad =>
      if ℓ + 1 < R then walkB f (.grid u (ℓ + 1))
      else ⟨u, u + B ℓ, ℓ, false, .bad⟩ :: walkB f (next R B (u + B ℓ))
  | f + 1, .free u =>
    if T ≤ u then [] else
    match g u with
    | .cov e => ⟨u, e, R, true, .cov e⟩ :: walkB f (next R B e)
    | .bev e j => ⟨u, e, R, true, .bev e j⟩ :: walkB f (next R B e)
    | .bad => ⟨u, u + 1, R, true, .bad⟩ :: walkB f (next R B (u + 1))

/-- Hypotheses on the outcome functions. -/
structure HypB : Prop where
  pos : ∀ r, 0 < B r
  dvd : ∀ r, r + 1 < R → B (r + 1) ∣ B r
  hR : 0 < R
  hT : B 0 ∣ T
  -- grid copies (entering level `r` at a level-`r` boundary `τ`)
  lb : ∀ τ r e, B r ∣ τ → τ < T → r < R → t τ r = .cov e → τ + B r ≤ e
  ub : ∀ τ r e, B r ∣ τ → τ < T → r < R → t τ r = .cov e → e ≤ T
  edvd : ∀ τ r e, B r ∣ τ → τ < T → r < R → t τ r = .cov e → B r ∣ e
  align : ∀ τ r e, B r ∣ τ → τ < T → r < R → t τ r = .cov e →
    ∀ j m, j < r → B j ∣ m → τ < m → m < e → B j ∣ e
  blt : ∀ τ r e j, B r ∣ τ → τ < T → r < R → t τ r = .bev e j → τ < e ∧ e ≤ T ∧ j ≤ r
  /-- No boundary of a level `< j` in `(τ, e]` (`j` = thread after the inheritance at `e`, see `Out.bev`). -/
  bnc : ∀ τ r e j, B r ∣ τ → τ < T → r < R → t τ r = .bev e j →
    ∀ i m, i < j → B i ∣ m → τ < m → m ≤ e → False
  -- finest continuous copies (entering at any round `u`)
  flt : ∀ u e, u < T → g u = .cov e → u < e ∧ e ≤ T ∧ B (R - 1) ∣ e
  falign : ∀ u e, u < T → g u = .cov e → ∀ j m, j < R → B j ∣ m → u < m → m < e → B j ∣ e
  fblt : ∀ u e j, u < T → g u = .bev e j → u < e ∧ e ≤ T ∧ j < R
  /-- As `bnc`, for free copies (`j` = thread after the inheritance at `e`). -/
  fbnc : ∀ u e j, u < T → g u = .bev e j → ∀ i m, i < j → B i ∣ m → u < m → m ≤ e → False

variable {R T B t g}

/-- P0057's hypotheses with an empty cover function: only the grid facts. -/
lemma HypB.base (h : HypB R T B t g) : Pool.P0057.Hyp R T B (fun _ _ => none) where
  pos := h.pos
  dvd := h.dvd
  hR := h.hR
  hT := h.hT
  lb := by intros; simp_all
  ub := by intros; simp_all
  edvd := by intros; simp_all
  align := by intros; simp_all

/-- The level-`j` epoch of `u` starts bad, or contains an earlier recorded (b′)-end of thread `≤ j`. -/
def Wit (t : ℕ → ℕ → Out) (B : ℕ → ℕ) (W : ℕ → ℕ → Prop) (j u : ℕ) : Prop :=
  t (est B j u) j = .bad ∨ ∃ p j', W p j' ∧ j' ≤ j ∧ est B j u < p ∧ p ≤ u

/-- Invariant of walk positions. -/
def InvB (R T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Out) (W : ℕ → ℕ → Prop) : Pos → Prop
  | .grid u ℓ => ℓ < R ∧ B ℓ ∣ u ∧ u ≤ T ∧ ∀ j < ℓ, Wit t B W j u
  | .free u => u ≤ T ∧ ∀ j < R, Wit t B W j u

lemma Wit.mono {W W' : ℕ → ℕ → Prop} (hW : ∀ p j, W p j → W' p j) {j u : ℕ} (hw : Wit t B W j u) :
    Wit t B W' j u := by
  rcases hw with hw | ⟨p, j', h1, h2, h3, h4⟩
  · exact Or.inl hw
  · exact Or.inr ⟨p, j', hW _ _ h1, h2, h3, h4⟩

/-- No level-`j` boundary in `(a, b]` keeps the level-`j` epoch. -/
lemma est_eq_of_nob {j : ℕ} (hpos : 0 < B j) {a b : ℕ} (hab : a ≤ b)
    (hn : ∀ m, B j ∣ m → a < m → m ≤ b → False) : est B j b = est B j a := by
  have h1 := est_le (B := B) j a
  have h2 := lt_est_add hpos a
  have hlt : b < est B j a + B j := by
    by_contra hc; push_neg at hc
    exact hn _ (dvd_add (est_dvd j a) dvd_rfl) h2 hc
  exact est_eq_of hpos (est_dvd j a) (by omega) hlt

lemma Wit.transfer {W : ℕ → ℕ → Prop} {j : ℕ} (hpos : 0 < B j) {a b : ℕ} (hab : a ≤ b)
    (hn : ∀ m, B j ∣ m → a < m → m ≤ b → False) (hw : Wit t B W j a) : Wit t B W j b := by
  have he := est_eq_of_nob hpos hab hn
  rcases hw with hw | ⟨p, j', h1, h2, h3, h4⟩
  · left; rw [he]; exact hw
  · right; exact ⟨p, j', h1, h2, by rw [he]; exact h3, by omega⟩

/-- A (b′)-end `e` off the level-`j` grid witnesses level `j ≥ j'`. -/
lemma Wit.ofEnd {W : ℕ → ℕ → Prop} {e j j' : ℕ} (hW : W e j') (hj : j' ≤ j) (hnd : ¬ B j ∣ e) :
    Wit t B W j e := by
  right
  refine ⟨e, j', hW, hj, ?_, le_rfl⟩
  rcases (est_le (B := B) j e).lt_or_eq with h | h
  · exact h
  · exact absurd (h ▸ est_dvd j e) hnd

section
variable (h : HypB R T B t g)
include h

lemma dvdR {j : ℕ} (hj : j < R) : B (R - 1) ∣ B j :=
  dvd_of_le h.base (by omega) (by have := h.hR; omega)

lemma inv_next {W : ℕ → ℕ → Prop} {e : ℕ} (hle : e ≤ T)
    (hw : ∀ j < R, ¬ B j ∣ e → Wit t B W j e) : InvB R T B t W (next R B e) := by
  unfold next
  split_ifs with hd
  · obtain ⟨hcl, hcd⟩ := canon_spec h.base hd
    exact ⟨hcl, hcd, hle, fun j hj => hw j (by omega) (canon_min h.base hj)⟩
  · exact ⟨hle, fun j hj => hw j hj (fun hj' => hd ((dvdR h hj).trans hj'))⟩

lemma inv_gcov {W : ℕ → ℕ → Prop} {τ r e : ℕ} (hI : InvB R T B t W (.grid τ r)) (hτ : τ < T)
    (he : t τ r = .cov e) : InvB R T B t W (next R B e) := by
  obtain ⟨hr, hd, -, hw⟩ := hI
  refine inv_next h (h.ub τ r e hd hτ hr he) fun j hj hnd => ?_
  have hBe := h.edvd τ r e hd hτ hr he
  have hjr : j < r := by
    by_contra hc; push_neg at hc
    exact hnd ((dvd_of_le h.base hc (by omega)).trans hBe)
  have hlb := h.lb τ r e hd hτ hr he
  refine (hw j hjr).transfer (h.pos j) (by have := h.pos r; omega) fun m hm h1 h2 => ?_
  rcases h2.lt_or_eq with h2 | h2
  · exact hnd (h.align τ r e hd hτ hr he j m hjr hm h1 h2)
  · exact hnd (h2 ▸ hm)

lemma inv_gbev {W : ℕ → ℕ → Prop} {τ r e j0 : ℕ} (hI : InvB R T B t W (.grid τ r)) (hτ : τ < T)
    (he : t τ r = .bev e j0) :
    InvB R T B t (fun p j => W p j ∨ (p = e ∧ j = j0)) (next R B e) := by
  obtain ⟨hr, hd, -, hw⟩ := hI
  obtain ⟨h1, h2, h3⟩ := h.blt τ r e j0 hd hτ hr he
  refine inv_next h h2 fun j hj hnd => ?_
  by_cases hjj : j0 ≤ j
  · exact Wit.ofEnd (Or.inr ⟨rfl, rfl⟩) hjj hnd
  · push_neg at hjj
    refine ((hw j (by omega)).mono fun p j h => Or.inl h).transfer (h.pos j) h1.le
      fun m hm hm1 hm2 => h.bnc τ r e j0 hd hτ hr he j m hjj hm hm1 hm2

lemma inv_gdescend {W : ℕ → ℕ → Prop} {τ r : ℕ} (hI : InvB R T B t W (.grid τ r))
    (hn : t τ r = .bad) (hr : r + 1 < R) : InvB R T B t W (.grid τ (r + 1)) := by
  obtain ⟨-, hd, hle, hw⟩ := hI
  refine ⟨hr, (h.dvd r hr).trans hd, hle, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact hw j hj
  · left; rw [est_eq_self hd]; exact hn

lemma inv_gfinest {W : ℕ → ℕ → Prop} {τ r : ℕ} (hI : InvB R T B t W (.grid τ r)) (hτ : τ < T)
    (hr : ¬ r + 1 < R) : τ + B r ≤ T ∧ InvB R T B t W (next R B (τ + B r)) := by
  obtain ⟨hrR, hd, -, hw⟩ := hI
  have hrR' : r = R - 1 := by omega
  have hle : τ + B r ≤ T := by
    obtain ⟨k, hk⟩ := hd
    obtain ⟨m, hm⟩ := (hrR' ▸ last_dvd_T h.base : B r ∣ T)
    have hp := h.pos r
    have : k < m := by
      by_contra hc; push_neg at hc
      have : B r * m ≤ B r * k := Nat.mul_le_mul_left _ hc
      omega
    calc τ + B r = B r * (k + 1) := by rw [hk]; ring
      _ ≤ B r * m := Nat.mul_le_mul_left _ this
      _ = T := hm.symm
  refine ⟨hle, inv_next h hle fun j hj hnd => ?_⟩
  have hjr : j < r := by
    by_contra hc
    exact hnd (by have : j = r := by omega
                  subst this; exact dvd_add hd dvd_rfl)
  refine (hw j hjr).transfer (h.pos j) (by omega) fun m hm hm1 hm2 => ?_
  have hmr : B r ∣ m := (dvd_of_le h.base hjr.le hrR).trans hm
  obtain ⟨k, hk⟩ := hd
  obtain ⟨k', hk'⟩ := hmr
  have hp := h.pos r
  have h1 : k < k' := by
    by_contra hc; push_neg at hc
    have : B r * k' ≤ B r * k := Nat.mul_le_mul_left _ hc
    omega
  have h2 : k' ≤ k + 1 := by
    by_contra hc; push_neg at hc
    have : B r * (k + 2) ≤ B r * k' := Nat.mul_le_mul_left _ hc
    nlinarith
  have : k' = k + 1 := by omega
  subst this
  exact hnd (by rw [hk, show B r * k + B r = B r * (k + 1) by ring, ← hk']; exact hm)

lemma inv_fcov {W : ℕ → ℕ → Prop} {u e : ℕ} (hI : InvB R T B t W (.free u)) (hu : u < T)
    (he : g u = .cov e) : InvB R T B t W (next R B e) := by
  obtain ⟨-, hw⟩ := hI
  obtain ⟨h1, h2, -⟩ := h.flt u e hu he
  refine inv_next h h2 fun j hj hnd => ?_
  refine (hw j hj).transfer (h.pos j) h1.le fun m hm hm1 hm2 => ?_
  rcases hm2.lt_or_eq with hm2 | hm2
  · exact hnd (h.falign u e hu he j m hj hm hm1 hm2)
  · exact hnd (hm2 ▸ hm)

lemma inv_fbev {W : ℕ → ℕ → Prop} {u e j0 : ℕ} (hI : InvB R T B t W (.free u)) (hu : u < T)
    (he : g u = .bev e j0) :
    InvB R T B t (fun p j => W p j ∨ (p = e ∧ j = j0)) (next R B e) := by
  obtain ⟨-, hw⟩ := hI
  obtain ⟨h1, h2, -⟩ := h.fblt u e j0 hu he
  refine inv_next h h2 fun j hj hnd => ?_
  by_cases hjj : j0 ≤ j
  · exact Wit.ofEnd (Or.inr ⟨rfl, rfl⟩) hjj hnd
  · push_neg at hjj
    refine ((hw j hj).mono fun p j h => Or.inl h).transfer (h.pos j) h1.le
      fun m hm hm1 hm2 => h.fbnc u e j0 hu he j m hjj hm hm1 hm2

lemma inv_fbad {W : ℕ → ℕ → Prop} {u : ℕ} (hI : InvB R T B t W (.free u)) (hu : u < T) :
    InvB R T B t W (next R B (u + 1)) := by
  obtain ⟨-, hw⟩ := hI
  refine inv_next h (by omega) fun j hj hnd => ?_
  refine (hw j hj).transfer (h.pos j) (by omega) fun m hm hm1 hm2 => ?_
  have : m = u + 1 := by omega
  exact hnd (this ▸ hm)

end

/-- Length of a record. -/
def len (x : RecB) : ℕ := x.stop - x.start

/-- Records charged by the count: covered records, and the finest bad records of the grid. -/
def counted (x : RecB) : Bool :=
  match x.out with
  | .cov _ => true
  | .bad => !x.free
  | .bev _ _ => false

/-- `p` is the end of a (b′)-record of thread `j` in `L`. -/
def IsBevEnd (L : List RecB) (p j : ℕ) : Prop := ∃ x ∈ L, x.out = .bev p j

/-- Records are consecutive from `τ` to `T`. -/
def ChainB (T : ℕ) : ℕ → List RecB → Prop
  | τ, [] => τ = T
  | τ, x :: l => x.start = τ ∧ τ < x.stop ∧ ChainB T x.stop l

/-- What a record of the walk satisfies. -/
structure RecOKB (R T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Out) (g : ℕ → Out) (W : ℕ → ℕ → Prop)
    (x : RecB) : Prop where
  lt : x.start < x.stop
  le : x.stop ≤ T
  grid : x.free = false → x.lvl < R ∧ B x.lvl ∣ x.start ∧ t x.start x.lvl = x.out
  free : x.free = true → g x.start = x.out
  cov : ∀ e, x.out = .cov e → e = x.stop
  bev : ∀ e j, x.out = .bev e j → e = x.stop
  bad : x.out = .bad → x.stop = x.start + (if x.free then 1 else B x.lvl) ∧
    (x.free = false → x.lvl + 1 = R)
  short : counted x = true → ∀ j < R, len x < B j →
    Wit t B W j x.start ∧ x.stop ≤ est B j x.start + B j

def posStart : Pos → ℕ
  | .grid u _ => u
  | .free u => u

def potB (R T : ℕ) : Pos → ℕ
  | .grid u ℓ => (T - u) * (R + 1) + (R - ℓ)
  | .free u => (T - u) * (R + 1)

section
variable (h : HypB R T B t g)
include h

lemma short_gcov {W : ℕ → ℕ → Prop} {τ r e j : ℕ} (hI : InvB R T B t W (.grid τ r)) (hτ : τ < T)
    (he : t τ r = .cov e) (hj : j < R) (hs : e - τ < B j) :
    Wit t B W j τ ∧ e ≤ est B j τ + B j := by
  obtain ⟨hr, hd, -, hw⟩ := hI
  have hlb := h.lb τ r e hd hτ hr he
  have hjr : j < r := by
    by_contra hc; push_neg at hc
    have := B_le_of_le h.base hc hj
    omega
  refine ⟨hw j hjr, ?_⟩
  have hpos := h.pos j
  have h1 : est B j τ ≤ τ := est_le j τ
  have h2 : τ < est B j τ + B j := lt_est_add hpos τ
  by_contra hc; push_neg at hc
  have hd' := h.align τ r e hd hτ hr he j (est B j τ + B j) hjr
    (dvd_add (est_dvd j τ) dvd_rfl) h2 hc
  obtain ⟨k, hk⟩ := est_dvd (B := B) j τ
  obtain ⟨m, hm⟩ := hd'
  have : k + 1 < m := by
    by_contra hc'; push_neg at hc'
    have : B j * m ≤ B j * (k + 1) := Nat.mul_le_mul_left _ hc'
    have : est B j τ + B j = B j * (k + 1) := by rw [hk]; ring
    omega
  have h3 : B j * (k + 2) ≤ B j * m := Nat.mul_le_mul_left _ this
  have h4 : B j * (k + 2) = est B j τ + 2 * B j := by rw [hk]; ring
  omega

lemma short_gfinest {W : ℕ → ℕ → Prop} {τ r j : ℕ} (hI : InvB R T B t W (.grid τ r))
    (hr : ¬ r + 1 < R) (hj : j < R) (hs : B r < B j) :
    Wit t B W j τ ∧ τ + B r ≤ est B j τ + B j := by
  obtain ⟨hrR, hd, -, hw⟩ := hI
  have hjr : j < r := by
    by_contra hc; push_neg at hc
    have := B_le_of_le h.base hc hj
    omega
  refine ⟨hw j hjr, ?_⟩
  have hpos := h.pos j
  have h2 : τ < est B j τ + B j := lt_est_add hpos τ
  have hm : B r ∣ est B j τ + B j :=
    (dvd_of_le h.base hjr.le hrR).trans (dvd_add (est_dvd j τ) dvd_rfl)
  obtain ⟨k, hk⟩ := hd
  obtain ⟨m, hm'⟩ := hm
  have hp := h.pos r
  have hkm : k < m := by
    by_contra hc'; push_neg at hc'
    have : B r * m ≤ B r * k := Nat.mul_le_mul_left _ hc'
    omega
  have : B r * (k + 1) ≤ B r * m := Nat.mul_le_mul_left _ hkm
  nlinarith

lemma short_fcov {W : ℕ → ℕ → Prop} {u e j : ℕ} (hI : InvB R T B t W (.free u)) (hu : u < T)
    (he : g u = .cov e) (hj : j < R) (hs : e - u < B j) :
    Wit t B W j u ∧ e ≤ est B j u + B j := by
  obtain ⟨-, hw⟩ := hI
  refine ⟨hw j hj, ?_⟩
  have hpos := h.pos j
  have h2 : u < est B j u + B j := lt_est_add hpos u
  by_contra hc; push_neg at hc
  have hd := h.falign u e hu he j (est B j u + B j) hj (dvd_add (est_dvd j u) dvd_rfl) h2 hc
  obtain ⟨k, hk⟩ := est_dvd (B := B) j u
  obtain ⟨m, hm⟩ := hd
  have : k + 1 < m := by
    by_contra hc'; push_neg at hc'
    have : B j * m ≤ B j * (k + 1) := Nat.mul_le_mul_left _ hc'
    have : est B j u + B j = B j * (k + 1) := by rw [hk]; ring
    omega
  have h3 : B j * (k + 2) ≤ B j * m := Nat.mul_le_mul_left _ this
  have h4 : B j * (k + 2) = est B j u + 2 * B j := by rw [hk]; ring
  omega

end

lemma RecOKB.mono {W W' : ℕ → ℕ → Prop} (hW : ∀ p j, W p j → W' p j) {x : RecB}
    (hx : RecOKB R T B t g W x) : RecOKB R T B t g W' x :=
  { hx with short := fun hc j hj hl => ⟨((hx.short hc j hj hl).1).mono hW, (hx.short hc j hj hl).2⟩ }

lemma posStart_next (e : ℕ) : posStart (next R B e) = e := by
  unfold next; split_ifs <;> rfl

lemma potB_next (e : ℕ) : potB R T (next R B e) ≤ (T - e) * (R + 1) + R := by
  unfold next; split_ifs <;> simp [potB]

lemma isBevEnd_cons {x : RecB} {L : List RecB} {p j : ℕ} (hp : IsBevEnd L p j) :
    IsBevEnd (x :: L) p j := by
  obtain ⟨y, hy, hy'⟩ := hp
  exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

section
variable (h : HypB R T B t g)
include h

lemma pot_step {u e f : ℕ} (hu : u < T) (hue : u < e) (heT : e ≤ T) (hf : (T - u) * (R + 1) ≤ f) :
    potB R T (next R B e) < f := by
  have := potB_next (R := R) (T := T) (B := B) e
  have : (T - e) * (R + 1) + (R + 1) ≤ (T - u) * (R + 1) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  omega

theorem walkB_spec : ∀ (f : ℕ) (pos : Pos) (W : ℕ → ℕ → Prop), InvB R T B t W pos →
    potB R T pos < f →
    ChainB T (posStart pos) (walkB R T B t g f pos) ∧
      ∀ x ∈ walkB R T B t g f pos,
        RecOKB R T B t g (fun p j => W p j ∨ IsBevEnd (walkB R T B t g f pos) p j) x
  | 0, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, .grid u ℓ, W, hI, hf => by
    unfold walkB
    by_cases hT : T ≤ u
    · rw [if_pos hT]
      exact ⟨le_antisymm hI.2.2.1 hT, by simp⟩
    rw [if_neg hT]
    push_neg at hT
    have hf' : (T - u) * (R + 1) ≤ f := by simp only [potB] at hf; omega
    obtain ⟨hr, hd, hle, hw⟩ := hI
    cases he : t u ℓ with
    | cov e =>
      have hlb := h.lb u ℓ e hd hT hr he
      have hub := h.ub u ℓ e hd hT hr he
      have hpos := h.pos ℓ
      have hI' := inv_gcov h ⟨hr, hd, hle, hw⟩ hT he
      obtain ⟨hc, hrs⟩ := walkB_spec f _ W hI' (pot_step h hT (by omega) hub hf')
      rw [posStart_next] at hc
      refine ⟨⟨rfl, show u < e by omega, hc⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨by simp; omega, hub, fun _ => ⟨hr, hd, he⟩, fun h' => by simp at h', fun e' h' => ?_,
          fun _ _ h' => by simp at h', fun h' => by simp at h', fun _ j hj hl => ?_⟩
        · simp only [Out.cov.injEq] at h'; exact h'.symm
        · obtain ⟨h1, h2⟩ := short_gcov h ⟨hr, hd, hle, hw⟩ hT he hj hl
          exact ⟨h1.mono fun p j hp => Or.inl hp, h2⟩
      · exact (hrs x hx).mono fun p j hp => hp.elim Or.inl fun hp => Or.inr (isBevEnd_cons hp)
    | bev e j0 =>
      obtain ⟨h1, h2, h3⟩ := h.blt u ℓ e j0 hd hT hr he
      have hI' := inv_gbev h ⟨hr, hd, hle, hw⟩ hT he
      obtain ⟨hc, hrs⟩ := walkB_spec f _ _ hI' (pot_step h hT h1 h2 hf')
      rw [posStart_next] at hc
      refine ⟨⟨rfl, h1, hc⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨h1, h2, fun _ => ⟨hr, hd, he⟩, fun h' => by simp at h', fun _ h' => by simp at h',
          fun e' j' h' => ?_, fun h' => by simp at h', fun hc => by simp [counted] at hc⟩
        simp only [Out.bev.injEq] at h'; exact h'.1.symm
      · refine (hrs x hx).mono fun p j hp => ?_
        rcases hp with (hp | ⟨rfl, rfl⟩) | hp
        · exact Or.inl hp
        · exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
        · exact Or.inr (isBevEnd_cons hp)
    | bad =>
      by_cases hr1 : ℓ + 1 < R
      · simp only [if_pos hr1]
        have hI' := inv_gdescend h ⟨hr, hd, hle, hw⟩ he hr1
        exact walkB_spec f _ W hI' (by simp only [potB] at hf ⊢; omega)
      · simp only [if_neg hr1]
        have hpos := h.pos ℓ
        obtain ⟨hle', hI'⟩ := inv_gfinest h ⟨hr, hd, hle, hw⟩ hT hr1
        obtain ⟨hc, hrs⟩ := walkB_spec f _ W hI' (pot_step h hT (by omega) hle' hf')
        rw [posStart_next] at hc
        refine ⟨⟨rfl, show u < u + B ℓ by omega, hc⟩, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · refine ⟨by simp; omega, hle', fun _ => ⟨hr, hd, he⟩, fun h' => by simp at h',
            fun _ h' => by simp at h', fun _ _ h' => by simp at h', fun _ => ⟨by simp, fun _ => show ℓ + 1 = R by omega⟩,
            fun _ j hj hl => ?_⟩
          simp only [len, Nat.add_sub_cancel_left] at hl
          obtain ⟨h1, h2⟩ := short_gfinest h ⟨hr, hd, hle, hw⟩ hr1 hj hl
          exact ⟨h1.mono fun p j hp => Or.inl hp, h2⟩
        · exact (hrs x hx).mono fun p j hp => hp.elim Or.inl fun hp => Or.inr (isBevEnd_cons hp)
  | f + 1, .free u, W, hI, hf => by
    unfold walkB
    by_cases hT : T ≤ u
    · rw [if_pos hT]
      exact ⟨le_antisymm hI.1 hT, by simp⟩
    rw [if_neg hT]
    push_neg at hT
    have hf' : (T - u) * (R + 1) ≤ f := by simp only [potB] at hf; omega
    cases he : g u with
    | cov e =>
      obtain ⟨h1, h2, -⟩ := h.flt u e hT he
      have hI' := inv_fcov h hI hT he
      obtain ⟨hc, hrs⟩ := walkB_spec f _ W hI' (pot_step h hT h1 h2 hf')
      rw [posStart_next] at hc
      refine ⟨⟨rfl, h1, hc⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨h1, h2, fun h' => by simp at h', fun _ => he, fun e' h' => ?_,
          fun _ _ h' => by simp at h', fun h' => by simp at h', fun _ j hj hl => ?_⟩
        · simp only [Out.cov.injEq] at h'; exact h'.symm
        · obtain ⟨h1, h2⟩ := short_fcov h hI hT he hj hl
          exact ⟨h1.mono fun p j hp => Or.inl hp, h2⟩
      · exact (hrs x hx).mono fun p j hp => hp.elim Or.inl fun hp => Or.inr (isBevEnd_cons hp)
    | bev e j0 =>
      obtain ⟨h1, h2, -⟩ := h.fblt u e j0 hT he
      have hI' := inv_fbev h hI hT he
      obtain ⟨hc, hrs⟩ := walkB_spec f _ _ hI' (pot_step h hT h1 h2 hf')
      rw [posStart_next] at hc
      refine ⟨⟨rfl, h1, hc⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨h1, h2, fun h' => by simp at h', fun _ => he, fun _ h' => by simp at h',
          fun e' j' h' => ?_, fun h' => by simp at h', fun hc => by simp [counted] at hc⟩
        simp only [Out.bev.injEq] at h'; exact h'.1.symm
      · refine (hrs x hx).mono fun p j hp => ?_
        rcases hp with (hp | ⟨rfl, rfl⟩) | hp
        · exact Or.inl hp
        · exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
        · exact Or.inr (isBevEnd_cons hp)
    | bad =>
      have hI' := inv_fbad h hI hT
      obtain ⟨hc, hrs⟩ := walkB_spec f _ W hI' (pot_step h hT (by omega) (by omega) hf')
      rw [posStart_next] at hc
      refine ⟨⟨rfl, show u < u + 1 by omega, hc⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by simp, by simp; omega, fun h' => by simp at h', fun _ => he, fun _ h' => by simp at h',
          fun _ _ h' => by simp at h', fun _ => ⟨by simp, fun h' => by simp at h'⟩,
          fun hc => by simp [counted] at hc⟩
      · exact (hrs x hx).mono fun p j hp => hp.elim Or.inl fun hp => Or.inr (isBevEnd_cons hp)

end


lemma chainB_sum_le : ∀ (L : List RecB) (τ : ℕ), ChainB T τ L → ∀ a b : ℕ,
    ((L.filter fun x => decide (a ≤ x.start ∧ x.stop ≤ b)).map len).sum ≤ b - max a τ
  | [], _, _, a, b => by simp
  | x :: L, τ, ⟨hs, hlt, hc⟩, a, b => by
    have ih := chainB_sum_le L x.stop hc a b
    by_cases hp : a ≤ x.start ∧ x.stop ≤ b
    · rw [List.filter_cons_of_pos (by simpa using hp), List.map_cons, List.sum_cons]
      have hl : len x = x.stop - x.start := rfl
      have : max a x.stop = x.stop := max_eq_right (by omega)
      rw [this] at ih
      have : max a τ = τ := max_eq_right (by omega)
      rw [this]
      omega
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      refine ih.trans ?_
      have : max a τ ≤ max a x.stop := max_le_max le_rfl (by omega)
      omega

lemma chainB_sum_len : ∀ (L : List RecB) (τ : ℕ), ChainB T τ L → (L.map len).sum = T - τ
  | [], τ, hc => by simp [ChainB] at hc; simp [hc]
  | x :: L, τ, ⟨hs, hlt, hc⟩ => by
    have ih := chainB_sum_len L x.stop hc
    have hle : x.stop ≤ T := by
      clear ih hs hlt
      induction L generalizing x with
      | nil => exact le_of_eq hc
      | cons y L' ihL => exact (le_of_lt hc.2.1).trans (ihL y hc.2.2)
    simp only [List.map_cons, List.sum_cons, ih, len]
    omega

/-- (b′)-records of thread `≤ j`. -/
def bevLe (j : ℕ) (x : RecB) : Bool :=
  match x.out with
  | .bev _ j' => decide (j' ≤ j)
  | _ => false

/-- Number of bad level-`j` epoch starts. -/
noncomputable def nBadB (T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Out) (j : ℕ) : ℕ :=
  ((Finset.range T).filter fun s => B j ∣ s ∧ t s j = Out.bad).card

/-- The walk from the origin with enough fuel. -/
noncomputable def theWalkB (R T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Out) (g : ℕ → Out) : List RecB :=
  walkB R T B t g (potB R T (.grid 0 0) + 1) (.grid 0 0)

section
variable (h : HypB R T B t g)
include h

/-- Short counted records lie in level-`j` epochs that start bad or contain a (b′)-end of thread `≤ j`. -/
theorem sum_shortB_le {L : List RecB} {τ0 : ℕ} (hc : ChainB T τ0 L)
    (hok : ∀ x ∈ L, RecOKB R T B t g (fun p j => IsBevEnd L p j) x) {j : ℕ} (hj : j < R) :
    ((L.filter fun x => counted x && decide (len x < B j)).map len).sum ≤
      B j * (nBadB T B t j + L.countP (bevLe j)) := by
  have hpos := h.pos j
  set S1 := (Finset.range T).filter fun s => B j ∣ s ∧ t s j = Out.bad
  set S2 := ((L.filter (bevLe j)).map fun x => est B j x.stop).toFinset
  have hS : ∀ x ∈ L, (counted x && decide (len x < B j)) = true → est B j x.start ∈ S1 ∪ S2 := by
    intro x hx hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hw, -⟩ := (hok x hx).short hp.1 j hj hp.2
    rcases hw with hb | ⟨p, j', ⟨y, hy, hy'⟩, hj', h1, h2⟩
    · refine Finset.mem_union_left _ ?_
      simp only [S1, Finset.mem_filter, Finset.mem_range]
      exact ⟨lt_of_le_of_lt (est_le j x.start) (lt_of_lt_of_le (hok x hx).lt (hok x hx).le),
        est_dvd j x.start, hb⟩
    · refine Finset.mem_union_right _ ?_
      have hyp : y.stop = p := ((hok y hy).bev p j' hy').symm
      have hest : est B j p = est B j x.start :=
        est_eq_of hpos (est_dvd j x.start) h1.le (lt_of_le_of_lt h2 (lt_est_add hpos _))
      simp only [S2, List.mem_toFinset, List.mem_map, List.mem_filter]
      refine ⟨y, ⟨hy, ?_⟩, by rw [hyp, hest]⟩
      simp [bevLe, hy', hj']
  have hcard : (S1 ∪ S2).card ≤ nBadB T B t j + L.countP (bevLe j) := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add (le_of_eq rfl) ?_)
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, List.countP_eq_length_filter]
  rw [Pool.P0057.sum_fiber L len _ (fun x => est B j x.start) (S1 ∪ S2) hS]
  calc ∑ s ∈ S1 ∪ S2, ((L.filter fun x => (counted x && decide (len x < B j)) &&
        decide (est B j x.start = s)).map len).sum
      ≤ ∑ s ∈ S1 ∪ S2, B j := by
        refine Finset.sum_le_sum fun s _ => ?_
        calc ((L.filter fun x => (counted x && decide (len x < B j)) &&
              decide (est B j x.start = s)).map len).sum
            ≤ ((L.filter fun x => decide (s ≤ x.start ∧ x.stop ≤ s + B j)).map len).sum := by
              apply Pool.P0057.sum_filter_mono
              intro x hx hp
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
              obtain ⟨⟨hcx, hl⟩, he⟩ := hp
              obtain ⟨-, hst⟩ := (hok x hx).short hcx j hj hl
              rw [he] at hst
              exact ⟨he ▸ est_le j x.start, hst⟩
          _ ≤ s + B j - max s τ0 := chainB_sum_le L τ0 hc s (s + B j)
          _ ≤ B j := by omega
    _ = B j * (S1 ∪ S2).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ B j * (nBadB T B t j + L.countP (bevLe j)) := Nat.mul_le_mul_left _ hcard

/-- **The walk with (b′)-ends.** Its records tile `[0, T)`, each satisfies `RecOKB` with witnesses among its
own (b′)-ends, and for every level `j` the counted records shorter than `B j` have total length at most
`B j · (#bad level-j epoch starts + #(b′)-records of thread ≤ j)`. -/
theorem theWalkB_spec :
    ChainB T 0 (theWalkB R T B t g) ∧
      (∀ x ∈ theWalkB R T B t g, RecOKB R T B t g (fun p j => IsBevEnd (theWalkB R T B t g) p j) x) ∧
      ((theWalkB R T B t g).map len).sum = T ∧
      ∀ j < R, (((theWalkB R T B t g).filter fun x => counted x && decide (len x < B j)).map len).sum ≤
        B j * (nBadB T B t j + (theWalkB R T B t g).countP (bevLe j)) := by
  have hI : InvB R T B t (fun _ _ => False) (.grid 0 0) :=
    ⟨h.hR, dvd_zero _, Nat.zero_le _, fun j hj => absurd hj (by omega)⟩
  obtain ⟨hc, hok⟩ := walkB_spec h _ _ _ hI (Nat.lt_succ_self _)
  have hok' : ∀ x ∈ theWalkB R T B t g,
      RecOKB R T B t g (fun p j => IsBevEnd (theWalkB R T B t g) p j) x :=
    fun x hx => (hok x hx).mono fun p j hp => hp.elim False.elim id
  refine ⟨hc, hok', ?_, fun j hj => sum_shortB_le h hc hok' hj⟩
  have := chainB_sum_len _ 0 hc
  simpa [theWalkB] using this

end

end Pool.P0135
