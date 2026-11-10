# Adversarial bandits with polylogarithmic memory: Õ(√(nT)) regret, a Lean 4 proof

This repository contains a machine-checked Lean 4 proof of the following theorem. A learner pulls **one arm per round**
and keeps only **polylog(nT) bits of memory**. Against oblivious adversaries it can still achieve expected regret
**Õ(√(nT))**, for all 1 ≤ n ≤ T. This matches the classical Ω(√(nT)) lower bound up to polylogarithmic factors.

## Read this first

- **AI-generated, not reviewed by a human.** The proof was produced by AI. No human has checked the Lean
  development or the modelling choices. No human-readable proof exists. `docs/PROOF_OUTLINE.md` is an outline written
  from the Lean code.
- **The guarantee is purely asymptotic. The constants are astronomical.** With the constants of the proof (proved
  in Lean, `Checks/Explicit.lean`):
  - memory ≤ 3·10^47·(log nT)^31 bits;
  - regret ≤ 2·10^95·√(nT)·(log nT)^60.

  Consequences:
  - The regret bound is at least T, and so says nothing, for every 2 ≤ n ≤ T ≤ 4·10^190 (proved in Lean,
    `Audit.bound_ge_T`).
  - It drops below T only around T ≈ 10^564 when n = 2 (numerical estimate, not in Lean).
  - For 2 ≤ n ≤ T ≤ 10^150 the explicit machine is simply "always pull arm 0" (proved in Lean, `Audit3E.famE_trivial`).
- **The main theorem is existential.** `Pool.P0294.main` selects its machines with `Classical.choose`.
  `Checks/FinitePrecision.lean` writes the construction out as definitions (`Audit3E.famE`) and proves the same bounds
  for it. Two opaque choices remain inside that construction: a sampler bijection (`Fintype.equivOfCardEq`) and one
  `Exists.choose`.
- **Only expected regret against an oblivious adversary is proved.** There is no high-probability bound and no
  adaptive adversary.
- **The probabilities in the main model are real numbers.** The main model lets a machine use arbitrary real
  transition probabilities. `Checks/FinitePrecision.lean` proves that any family meeting the target can be rounded:
  - each round then uses polylog(nT) fresh fair coins;
  - the state set is the same;
  - the regret grows by at most 1.

  The result therefore also holds in a strict finite-precision model (`Audit3.pool_refModel`).
- **What you have to trust:**
  - the Lean 4 kernel (v4.36.0-rc2);
  - Mathlib at commit `9d581df` (tag v4.36.0-rc2), whose `.olean` files are not re-checked;
  - the checker `check/Check.lean`.

  The axioms used are `propext`, `Classical.choice` and `Quot.sound` only. There is no `sorry` and no
  `native_decide`.

## 1. The problem

**Setting.**
- There are `n` arms and a horizon of `T` rounds, with `1 ≤ n ≤ T`.
- An *oblivious* adversary fixes a loss table `ℓ_t(i) ∈ {0, 1}` (rounds `0 ≤ t < T`, arms `i`) before the game starts.
- In round `t` the learner pulls one arm `a_t`, suffers `ℓ_t(a_t)`, and observes only that bit (bandit feedback).

**Learners with bounded memory.** A learner for `(n, T)` is a randomized finite-state machine:
- a finite set of states `S`;
- an initial distribution on `S`;
- in round `t`, in state `s`, it draws the arm `a_t` from a distribution `act(s)`, using fresh random coins;
- it then observes the bit `ℓ_t(a_t)` and moves to a state drawn from `next(s, a_t, ℓ_t(a_t))`, again with fresh coins.

The machine is *time-homogeneous*: `act` and `next` do not depend on `t`. A learner that needs a clock must store it in
its state. The state is the only thing carried from one round to the next. Random bits are free, but nothing random
persists outside the state.

**Memory** is `log₂ |S|` bits. It is a bound on the whole state set, so it holds on every execution path.

**Regret** is the expected total loss over rounds `0, …, T−1`, minus the total loss of the best fixed arm in hindsight:

    Regret = E[ Σ_{t<T} ℓ_t(a_t) ] − min_i Σ_{t<T} ℓ_t(i).

The expectation is over the learner's coins.

**The question.** What regret can learners with polylog(nT) bits of memory achieve? Any learner, with any memory, has
regret Ω(√(nT)) on some table. The target is to match this up to polylog factors.

The target holds if there are constants `C, k, C', k'` and, for every `1 ≤ n ≤ T`, a time-homogeneous machine
`F(n, T)` such that:
- `log₂ |S| ≤ C·(log nT)^k`;
- `Regret(F(n, T), ℓ) ≤ C'·√(nT)·(log nT)^k'` for every loss table `ℓ`.

**Strict (finite-precision) version.** As above, with these extra requirements:
- the initial state is deterministic;
- each round, `act` and `next` are deterministic functions of the state, the observed bit and `b` fresh fair coins,
  with `b ≤ C·(log nT)^k`.

Every probability is then a dyadic rational with denominator `2^b`. This is `Audit3.StrictTarget` in
`Checks/FinitePrecision.lean`. It is defined without any `Pool` definition, with the expectation written as a plain average over all coin tapes.

**Prior results.**

| Source | Pulls per round | Regret with polylog memory | Status |
|---|---|---|---|
| Braverman, Garg, Wang, Woodruff, Zhou, SODA 2026 (arXiv:2601.03533), Thm. 3 | 1 | n·T^{2/3}·polylog | published (vacuous once n ≥ T^{1/3}) |
| Same paper, Thm. 1 | 2 (one extra free observation) | √(nT)·polylog | published |
| Brukhim, Cesa-Bianchi, Ciliberto (arXiv:2603.00803), Thm. 17 | 1 | n^{1/3}·T^{2/3}·polylog (claimed) | preprint; the authors list √(nT) with polylog memory as open |
| Classical lower bound | any | Ω(√(nT)) for any memory | |
| **This repository** | **1** | **√(nT)·polylog, for all 1 ≤ n ≤ T** | Lean proof, see the caveats above |

In words: with a single pull per round and polylog memory, there is no polynomial regret penalty. The extra free
observation used by the √(nT) bound of Braverman et al. is not needed.

## 2. The formal statements

**The model and the target** are in `Pool/P0001/Model.lean` (machines, state law, regret, memory) and
`Pool/P0001/Targets.lean`:

```lean
def MinimaxPolylogAchievable : Prop :=
  ∃ F : Family, (∀ n T hn, (F n T hn).IsHomogeneous) ∧
    (∃ (C : ℝ) (k : ℕ), MemoryBound F C k) ∧
    ∃ (C' : ℝ) (k' : ℕ), RegretBound F fun n T => C' * Real.sqrt (n * T) * Real.log (n * T) ^ k'
```

**The main theorem** is in `Pool/P0294/Statement.lean`:

```lean
theorem Pool.P0294.main : Pool.P0001.MinimaxPolylogAchievable
```

**The same statement with Mathlib definitions only.** `Checks/Statement.lean` is about 40 lines and does not import
the `Pool` library. It defines `Restated.Achievable`. `Checks/Bridge.lean` proves
`Restated.achievable : Restated.Achievable` from `Pool.P0294.main`. To check what is proved without reading `Pool`, it
is enough to read `Checks/Statement.lean` and run the checks below.

**Further checks** (`Checks/`):

| Declaration | File | Content |
|---|---|---|
| `Restated.achievable` | `Bridge.lean` | the main theorem, in the Mathlib-only formulation |
| `Audit3.strict_of_minimax` | `FinitePrecision.lean` | any family meeting the target can be rounded to fair coins: same states, polylog coins per law, regret + 1 |
| `Audit3.pool_refModel` | `FinitePrecision.lean` | the strict fair-coin target `Audit3.StrictTarget` holds |
| `Audit3E.famE_spec` | `FinitePrecision.lean` | the construction behind the main theorem, written as definitions (`famE`), meets the target |
| `Audit3E.famE_trivial` | `FinitePrecision.lean` | for `2 ≤ n ≤ T ≤ 10^150`, `famE` is the one-state machine that always pulls arm 0 |
| `Audit.explicit_numeric` | `Explicit.lean` | explicit constants: memory ≤ 3·10^47·log(nT)^31, regret ≤ 2·10^95·√(nT)·log(nT)^60 |
| `Audit.bound_ge_T` | `Vacuous.lean` | that regret bound is ≥ T for 2 ≤ n ≤ T ≤ 4·10^190 |

## 3. How to check

Requirements:
- [elan](https://github.com/leanprover/elan), which installs the Lean version given in `lean-toolchain`;
- git;
- about 8 GB of disk for Mathlib and its build cache;
- about 16 GB of RAM (more for parallel replays, see below).

```bash
lake exe cache get      # download Mathlib's prebuilt .olean files
lake build              # builds the proof (230 modules) and the checks
scripts/verify.sh       # build + kernel replay of every module + statements and axioms of the main declarations
```

`scripts/verify.sh` writes its logs to `verify_out/` and ends with `ALL CHECKS PASSED`. It does three things:
1. It runs `lake build` and fails on any `sorry` or error.
2. It replays every module of `Pool` and `Checks` in the Lean kernel (`check/Check.lean --replay`). This catches
   constants that entered the environment without kernel checking.
3. It prints the statements of the main declarations and walks their axioms (`check/Check.lean --decls`). The walk does
   not rely on the `#print axioms` cache stored in `.olean` files.

Measured on a fresh clone with 8 CPU cores and a 28 GB memory limit:
- `lake exe cache get` took under a minute (9,081 files);
- `scripts/verify.sh` took about 10 minutes, including the build (`lake build` alone takes about 5 minutes);
- result: 237 of 237 modules replayed (9,077 constants), and every main declaration uses only `propext`,
  `Classical.choice` and `Quot.sound`.

With less memory, use fewer parallel replays: `JOBS=2 scripts/verify.sh`.

## 4. How the proof is organised

- `Pool/` has 230 modules, about 65,000 lines. A module `Pool/P####/` is one unit of the development. The numbers
  follow the order in which the units were written and carry no other meaning.
- `Pool.lean` imports all of them. All of them are needed for `Pool.P0294.main`; the rest of the development was left
  out.

The main line of the argument:

| Module | Role |
|---|---|
| `P0001` | the model and the target statement |
| `P0055`, `P0067` | subsampled play: run a learner on a random fraction of the rounds |
| `P0161`, `P0173` | reduction: the target follows from one "boosting step" applied recursively, at a fixed rate q = 1/polylog |
| `P0201`, `P0284` | the one-level machine: Peng–Rubinstein-style threaded pools of candidate arms, probed at thread-dependent rates, evicted against an independent base learner, with a sleeping-experts Hedge over the pool |
| `P0278`, `P0292` | the regret of one level in terms of the base learner's regret on a subsample |
| `P0294` | the last estimate (the probing remainder) and the main theorem |

`docs/PROOF_OUTLINE.md` describes the algorithm and the regret analysis in more detail, with pointers to the modules.

The comments inside the modules were written along the way. They can be imprecise, for example about exponents. The
Lean statements are authoritative.

## 5. Layout

| Path | Content |
|---|---|
| `Pool/`, `Pool.lean` | the proof |
| `Checks/`, `Checks.lean` | the Mathlib-only restatement, the finite-precision and explicit-construction checks, the explicit constants |
| `check/Check.lean` | kernel replay and axiom walk |
| `scripts/verify.sh` | the full check |
| `docs/PROOF_OUTLINE.md` | algorithm and proof outline |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | pinned Lean and Mathlib versions |
| `LICENSE` | Apache License 2.0 |

## License

Apache License 2.0, see `LICENSE`. `replayModule` in `check/Check.lean` follows lean4checker
(https://github.com/leanprover/lean4checker), which is also Apache-2.0.
