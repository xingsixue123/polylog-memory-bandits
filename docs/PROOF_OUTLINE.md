# How `Pool.P0294.main` is built: algorithm and proof outline

> This outline was written from the Lean sources. It is a guide for reading them, not a proof: correctness rests on the
> Lean kernel. Module names such as `P0284` refer to `Pool/P0284/`. The explicit constants are proved in
> `Checks/Explicit.lean` (`Audit.explicit_numeric`).

**Statement.** `P0001.MinimaxPolylogAchievable` asks for a family of homogeneous finite-state machines F(n,T). Each round the machine draws its arm from the current state with fresh coins and sees only that arm's loss bit; nothing but the state persists between rounds. The family needs memBits = log₂|S| ≤ C·log(nT)^k, and, for every oblivious table ℓ ∈ {0,1}^{T×n} and all 1 ≤ n ≤ T, an expected regret of at most C'·√(nT)·log(nT)^{k'}. The explicit version, `Audit.explicit_numeric` (`Checks/Explicit.lean`), has: **k = 31, C = 3·10^47, k' = 60, C' = 2·10^95**.

## 1. The algorithm

### One level: `machF(n,T,q,A)` (P0284 on top of P0201/P0194/P0176/P0261)
The inputs are a rate q with n/T ≤ q ≤ 1/32 and a homogeneous BASE learner A. Everything runs at the process horizon Tp = 2^⌈log₂T⌉ ∈ [T, 2T]. Let Λ = ⌊log₂(nTp)⌋ + 4.
- **Threads.** There are D = log₂Tp + 1 threads. Thread j has epochs of B_j = 2^{D−1−j} rounds, so B_0 = Tp and the finest thread has 1-round epochs.
- **Candidate copies.** A copy is a triple (arm, entry τ, thread j) with B_j | τ, and each copy is sampled independently with probability 1/n. So each thread gets about one candidate per epoch start.
- **Probe rates.** x_j = 1/max(Kc, min(Bm, ⌊Tp/(nB_j)⌋)), where Kc = 4D²·Sl·⌈1/q⌉ ≈ polylog/q and Bm ≈ √(T/n). Coarse threads are probed at the cap 1/Kc ≈ q/polylog, and fine threads at the floor x_f = 1/max(Kc, Bm). In between, x_j ≈ nB_j/T. There are Sl ≈ 6·10^5·Λ^11 slots per thread.
- **Round kinds.** A fresh coin chooses the kind of each round: BASE with probability w_B = q/2; slot (j,k) with probability x_j each, for a total Σ_j Sl·x_j ≤ q/4; exploitation with probability w_E ≥ 1/2.
- **Play** (`P0194.play`).
  - BASE round: BASE's arm, drawn with a fresh coin.
  - Exploitation round: ALG's draw, where the meta-arm means BASE's arm.
  - Slot (j,k): the k-th active member of thread j in entry order, or BASE's arm if that slot is empty or retired.
- **Data.** An observed member gains kx_j·ℓ = ℓ/x_j, importance-weighted at its *current* thread's rate. A retired member gains a fake +1 per round. BASE is updated only on BASE rounds, and B̂ += ℓ/w_B there.
- **Eviction 1: rule (b″), retirement** (`P0194.rhD`). At rounds u with Bm | u+1, member x is retired if (its data since entry) − (B̂ since entry) ≥ Λ(x,u). The margin is `ΛPc` (P0250/P0268/P0275): the ALG constants Lt/κ + α_T + Lc/(2w_Eγ), plus the BASE width, plus a thread-aware slot width Wocc(age), plus a "bank" w_j that pays for coarser walk records. The age is capped at the thread's lifetime. A retired member leaves ALG and its slot.
- **Eviction 2: merges** (Peng–Rubinstein Baseline+ with inheritance; P0030/P0042/P0052/P0065/P0176).
  - When a coarse epoch starts, finer threads restart and their sub-pools move to that thread, so a member's rate never decreases.
  - At epoch ends, levels 0..lev are merged by K iterations of a filter round. A Bernoulli(1/Qd) filter set F is drawn, and every non-filter member covered by an F-chain (length ≤ log₂Tp + 2, margin θ = max(Kc, Bm), estimated data) is removed.
- **ALG** (P0089/P0212/P0225/P0236). A dyadic sleeping Hedge over the active members plus the BASE meta-arm, run only on exploitation rounds.
  - η = IX parameter γ = 1/s, with s = √(qTp/n). The IX estimates are on a 1/⌈s⌉ grid.
  - It plays the Hedge marginal rounded to multiples of 1/⌈s⌉. A self-rounding normaliser perturbation makes it equal to an integer finite-state twin.
- **State** (P0201): the pools (≤ Ns = D·Sl copies, each with its level, retired flag and BASE count at entry), an Ns² table of pairwise cumulative estimated losses, BASE's state, the B̂ counter, the ALG twin, a clock in [0, Tp], and the stored action coin. There is one dummy round.

### Recursion (P0161/P0173/P0278)
Set Λ_H = c·(ln(nH)+1)^30 with c ≈ 9.33·10^37, and q_H = 1/(32Λ_H²).
- If H ≤ (12Λ_H²)²·n, use the one-state machine.
- Otherwise use machF(n, H, q_H, A), where A is the machine for horizon H' = ⌈4q_H·H⌉ = ⌈H/(8Λ_H²)⌉.

The depth is about ln(H/(144Λ⁴n))/ln(8Λ²), that is O(log T/log log T). In expectation BASE gets about q_H·Tp/2 ≤ q_H·H updates.

## 2. The regret analysis
1. **Fixed point** (`P0173.exists_machineIn`, `P0161.step_arith`). With √(1/q) = √32·Λ and √(8q) = 1/(2Λ), the bound R(H) = 12Λ²√(nH) satisfies Λ(√(nH/q) + R(⌈4qH⌉)) ≤ 12Λ²√(nH). Constants do not compound.
2. **BASE transfer** (`P0278.stepAtIn_of_famHypAt`, `P0067.regret_Sub_le_fixed`, `tail_le_exp`, `P0140.regret_prefix_le`).
   - BASE's policy enters with weight β ≤ 2γ = q against regret(Sub(A, q/2)) over Tp ≤ 2T rounds.
   - Subsampling gives regret(Sub) ≤ (2/q)(R_A(⌈4qT⌉) + 2/q).
   - So β·regret(Sub) ≤ 2R_A + 4√(nT/q).
3. **Horizon** (`P0140.regret_zeroAfter`). Regret over T equals regret over Tp+1 on the zero-padded table.
4. **Machine = process** (P0206, `P0214.sum_expLoss_le_intended`). E[machine loss] ≤ E[1 + process loss + Tp·1{overflow}].
5. **Split** (`P0194.condLoss_eq`, `P0210.regret_split_base`, `P0202.horizon_bPol_sub_le_regret`, `P0217.regret_le_base`). Per round:
   E[loss] − ℓ(i*) = (w_B + X₁)(BASE − i*) + w_E(ALG − i*) + Σ_s x_s(slot_s − BASE),
   with X₁ = Σ_s x_s. The BASE term is ≤ regret(Sub(A, w_B)).
6. **Probing** (P0209, P0154/P0162, P0211/P0219, P0203/P0216, `P0255.probe_le_restD2`, `P0258.slot_expect_path2`).
   - Each member pays Σ_u rate_u·(ℓ_u(y) − BASE_u).
   - Abel summation over nondecreasing rates gives rate_end·gap_end plus, for each jump, (jump size)·(lead over BASE).
   - Since (b″) has not fired, the estimated gap is below Λ. Concentration turns the estimated gap into the true one.
   - The jump credit, grouped by destination thread, is ≤ κ·Σ(BASE − ALG) + per-interval terms, where κ = (ΣSl)(Σx) ≤ q/4.
   - A copy at the floor rate costs at most x_f times its window.
7. **Absorption** (`P0234.absorb_le`, `P0258.regret_le_absorbedP2`). Since κ(BASE − ALG) = κ(BASE − i*) − κ(ALG − i*), BASE's weight becomes w_B + X₁ + κ ≤ q.
8. **ALG term** (P0186 walk, P0135/P0153 records, P0160/P0193/P0148 certificates, P0249, P0185/P0207/P0259 bad counts, P0243 budgets, `P0291.algT_famM_le`).
   - Comparator copies are forced in copy-last, which does not change the pools.
   - The records are of three kinds:
     - covered: ALG ≤ chain + θ + widths + Hedge;
     - retired: ALG ≤ BASE + ρ ≤ copy − bank;
     - bad: E[count] ≤ 4·10^5·n·Λ^12.
   - Total: ≤ 5·10^15·Λ^28·√(nT/q) + w_E·Tp·E[ovf].
9. **Overflow and bad events** (P0221/P0287, P0283/P0257, `P0292.Tp_badB_le`). Tp·E[ovf] ≤ 1, and the bad term is ≤ 3.
10. **Probing remainder** (`P0289.exp_goodTermP2_twin`, P0282, `P0294.goodBound`). It is ≤ K₀ + K₁·Tp·C_b ≤ 10^17·Λ^30·√(nT/q).
11. **Assembly** (`P0292.regret_famM_le`, `famHyp_of_good`). This gives FamHyp(CF, 30): regret ≤ CF·Lg^30·√(nT/q) + β·regret(Sub(A, q/2)). Steps 2 and 1 then close the recursion.

## 3. Memory
- **Per level** (`P0201.memBits_mach_le`, `P0284.memBits_machF_Lg`): bits(A) + 160·600001²·5^26·Lg^26 ≈ 8.6·10^31·Lg^26 bits.
  - The pairwise table dominates: Ns² entries of log₂(Tp(Kc+Bm+1)+1) bits, with Ns ≤ 6·10^5·Λ^12.
  - The copy records, ALG twin, clock, counters and coins are lower order.
- **Recursion.** It charges c·Lg^30 per level, over at most log₂H levels, which gives memBits ≤ log₂H·Λ_H.
- **Randomness.** Only fresh coins are used. Sampling and filter bits are drawn when needed, and nothing random persists outside the state.

## 4. Exponents and constants
- **Proved in Lean** (`Audit.explicit_raw`): Cg = 10^17·5^30, kg = 30, k = max(28, 30) = 30.
  - CF = 6 + 5·10^15·5^28 + Cg + 160·600001²·5^26, and c = CF + 6 ≈ 9.33·10^37 ≤ 10^38.
  - Memory: 2c·2^30 ≈ 2.0·10^47 times log^{k+1} = log^31.
  - Regret: 12c²·4^30 ≈ 1.2·10^95 times √(nT)·log^{2k} = √(nT)·log^60.
- **Galactic constants.**
  - The first non-trivial level appears near T ≈ 10^525 (n = 2).
  - The bound drops below T only for T ≳ 10^564 (numerical, not in Lean).
  - Lean (`Audit.bound_ge_T`) shows the bound is ≥ T for 2 ≤ n ≤ T ≤ 4·10^190.
- **Slack.** The per-level analysis gives memory exponent 26 and regret exponents 28/30. The exponents were never optimised.

## 5. What is new
- **Compared with Braverman, Garg, Wang, Woodruff and Zhou (SODA 2026, arXiv:2601.03533).**
  - Their single-query algorithm explores uniformly at rate γ and pays γT, which gives T^{2/3}.
  - Here probes are charged against an independent reference learner BASE: empty and retired slots play BASE, so a probe costs x·(member − BASE).
  - Rule (b″) caps each member's cost at about x·Λ ≈ √(x·D).
  - The weight q on BASE turns exploration into q·(BASE's regret), which is about R_B(qT) and not γT.
  - Eviction references BASE and not ALG, so nothing reads ALG. That keeps Peng–Rubinstein's passive-copy coupling valid with one query.
- **Compared with Peng and Rubinstein (arXiv:2303.01673).**
  - Reused: sampling at 1/n, threads with inheritance, the merge lemma (with chain covers in place of their benchmark cover) and the bad-epoch walk.
  - New: thread-dependent probe rates with an Abel/credit lemma whose cost is absorbed into BASE's coefficient, and the self-similar recursion. In that recursion, BASE is the same machine on a q/2-subsample, its regret transfers with factor 2, and q = 1/polylog is a fixed point.
- **Where the new idea is.** It sits in the one-level step FamHyp: regret Õ(√(nT/q)) + 2R_B(4qT), built from BASE-referenced eviction and thread-dependent probe rates with the credit lemma. The recursion (P0161) and subsampling (P0055/P0067) are routine.
