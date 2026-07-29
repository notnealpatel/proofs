# Handoff — Erdős 20, ω program, and group sieve

You are an orchestrator for an interactive research session
with the principal mathematician on this project. Read this
document fully before acting.

## Session posture

You have latitude to propose directions and assess proof
state. You must confirm with the user before dispatching
agents or committing to a direction. The user is the
mathematician; you steer by their judgment.

## Project conventions

- Lean 4 proofs: `~/p/proofs/Proofs/Proofs/`
- Mathlib: `.lake/packages/mathlib/`
- Library code: `Proofs/Xlib/`
- Scratch: `Scratch.lean` for `#check`/`#eval`/`example`
- Build: `flock .lake/agent.lock lake build` from
  `~/p/proofs/Proofs/` only. Never the parent directory.
- Sieve programs: `Scratch/GroupSieve/`
- Go programs: `cmd/`
- Ground claims with `sage`, `wiki`, `oeis`, `erdos` skills.
  Never answer from training data on mathematical facts.

## Task card housekeeping

Run `goof tasks ready` on startup. Current state (as of
2026-07-15):

**Close immediately** (work is done, card not updated):
- `Ep542` — `SchinzelSzekeres.lean` exists and compiles
- `Pf4` — `DihedralTPP/` exists and compiles

**In-scope** (genuine open math):
- `Pf3` — abelian direct factor invariance ρ₀(A×G) = ρ₀(G).
  The ≤ direction is the novel content (checked 7 sources,
  stated nowhere). The ≥ direction is known (Murthy thesis
  Lemma 4.8). Card at `.tasks/f5exp/cards/Pf3.md`. Three
  prior agent attempts crashed on infrastructure, zero proof
  work done. Proof skeleton: centre-intersection induction
  + residual Goursat case. Fallback: prime-order A only.
  Sieve data shows 88% of 2-power peels are C₂ — even the
  C_p case carries most rejection payoff.

**Blocked on Pf3**:
- `Im6` — product decomposition tier for the sieve. Scope
  depends entirely on Pf3's outcome (proof → new tier,
  counterexample → harness anchor).

**All other cards**: done. The DAG has ~66 cards total;
the three above are the only live ones.

---

## Thread 1: Erdős 20 — sunflower conjecture

Seven sorry-free files in `Proofs/Proofs/Erdos20/`.

### Headline result

`sunflower_of_large_family` at `SpreadLemma.lean:2801`:

```
theorem sunflower_of_large_family {s k : ℕ} (hs : 1 ≤ s)
    {F : Finset (Finset (Fin n))} (hunif : ∀ S ∈ F, S.card = k)
    (hcard : ((884736 * s * (Nat.log 2 k + 1) : ℕ) : ℚ) ^ k
             < (F.card : ℚ)) :
    HasSunflower F s
```

Full ALWZ/Rao/BCW improved sunflower lemma for **general**
k-uniform families. First ITP formalization of any improved
sunflower bound. The only prior is the classical (r−1)^k·k!
in Isabelle/AFP (Thiemann 2021).

### What's closed

The improved bound is **done**. The sunflower **conjecture**
(purely exponential C(s)^k, no log k) remains open — the log
factor is intrinsic to the spread-lemma approach (m = O(log k)
iteration steps). Closing the conjecture needs a new idea.

### File dependency chain

```
Sunflower.lean (root — shift infrastructure)
├── ShiftedSunflower.lean (shifted-family bound, shadow bound)
│   ├── ShadowLadder.lean (iterated: |F|·k! ≤ ∏ τ(∂ⁱF))
│   └── Counterexample.lean (refutes Mishra v1 Lemma 3)
├── Spread.lean (R-spread, regularization, link-local reduction)
│   └── SpreadDefect.lean (anti-spread |F| ≤ r^k, bridge refutation)
│       └── SpreadLemma.lean (THE spread lemma, 2820 lines)
```

### Key theorems by file

**Sunflower.lean** — `franklShift_card` (|C_ij F| = |F|),
`sunflowerNumber_franklShift_le` (τ(C_ij F) ≤ 2τ(F)),
`matchingNumber_reachable` (matchings transport backward),
`empty_kernel_sunflower_le_sunflowerNumber`.

**ShiftedSunflower.lean** —
`card_mul_le_sunflowerNumber_mul_shadow` (k|F| ≤ τ(F)|∂F|),
`IsShiftedFrom.star_card_half` (|A₁| ≥ |F|/2),
`IsFullyCompressed.hasSunflower` (s^{2(s−1)}·2^k bound),
`exists_isFullShiftOf` (shift endpoints exist).

**Counterexample.lean** — `shifting_creates_stars` (τ=2 →
τ=17), `mishra_v1_lemma3_false` (no bound 3τ²+τ+1 holds).
4-uniform family on Fin 20, 190-step lex chain, native_decide.

**Spread.lean** — `IsRSpread` (ALWZ Def 1.10, division-free
over ℚ), `exists_popular_witness`, `exists_isRSpread_linkAt`
(regularization), `hasSunflower_of_forall_isRSpread` (spread
lemma as explicit hypothesis → sunflower for general families).

**SpreadDefect.lean** —
`card_le_pow_of_forall_linkAt_not_isRSpread` (anti-spread
|F| ≤ r^k), `spread_defect_unbounded` / `_bridge_false`
(refutation at r* ≥ 4).

**SpreadLemma.lean** — MNSZ second-moment route. `IsProbW`,
`IsSpreadW` (spread measure), `biasedW` (q-biased law),
`second_moment_bound` (E[Z²] ≤ 6c²), `one_step` (one-step
contraction ≤ 6c), `nextW` / `trajW` / `fullW` (multi-step
coupling), `fail_prob_le` (failure ≤ 24c), `spread_lemma_core`
(core with free parameters), `spread_lemma` (packaged for
r-spread families), `sunflower_of_large_family` (headline).

### Open threads

- Constant 884736: the paper gives ~10⁸; this is tighter
  but not optimized.
- `shadow_ladder` (ShadowLadder.lean:34): |F|·k! ≤ ∏ τ(∂ⁱF).
  Not found stated in the literature. The "ladder ≡ conjecture"
  framing is refuted (SpreadDefect.lean).
- Counterexample publishability: machine-checked refutation
  of a claimed sunflower-conjecture proof.
- SpreadDefect.lean:161–195 identifies three frontier questions
  on τ-transport growth rate.

---

## Thread 2: the ω program

First ITP formalization of algebraic complexity theory. Four
sub-campaigns in `Proofs/Proofs/`, library code in `Xlib/`.

### Sorry-free proof inventory (Proofs/Proofs/)

**BilinearComplexity/** (10 files, all sorry-free):
- `rank_matMulTensor_eq_seven` (Strassen + Winograd, ℤ)
- `sq_le_rank_matMulTensor` (flattening: n² ≤ R⟨n,n,n⟩)
- `rank_matMulTensor_mul_le` (Kronecker submultiplicativity)
- `rank_matMulTensor_mono` (dimension monotonicity)
- `rank_matMulTensor_cyc` (S₃ symmetry: R⟨a,b,c⟩ = R⟨b,c,a⟩)
- `rank_matMulTensor_two_pow_le_real` (R⟨2ᵐ,2ᵐ,2ᵐ⟩ ≤ 7ᵐ)
- `sliceRank_diag` (Tao diagonal: exact slice rank)
- `rank_matMulTensor_le_of_isTPP` (Murthy 4.13: TPP → rank)
- `omega := sInf omegaSet`, `two_le_omega`, `omega_le_three`,
  `omega_lt_three`, `omega_le_logb_two_seven`

**CHILO/** (2 files, sorry-free):
- `trace_cyclicBlock_mul_cyclicBlock_mul_cyclicBlock`:
  tr(X³) = 3·tr(ABC)
- `conner_waring`: rank-18 Waring decomposition of sM₃

**DihedralTPP/** (2 files, sorry-free):
- `card_mul_le_of_isTPP`: 3|S||T||U| ≤ 8n (ρ(D₂ₙ) ≤ 4/3)
- `tppCapacity_dihedralGroup_six`: β(D₁₂) = 16

**Vp2/** (4 files, sorry-free):
- `Circuit` inductive + `VPFamily` (first ITP VP class)
- `BorderRankLE` as polynomial closure (Nullstellensatz)
- `vanishingIdeal_test111Locus_le` (apolarity soundness)
- `Vp2OpenQuestion`: named Prop, not theorem — no source
  proves or refutes it
- `passes111_of_borderRankLE`: soundness anchor (needs
  `[Infinite k]`)
- `exists_flattening_vpDistinguisher`: flattening minors are
  VP-natural proofs (the SUPPORTED fact)

### Cross-campaign edge

`GroupTensor.lean` imports `DihedralTPP.Basic` — the sole
cross-campaign dependency. `rank_matMulTensor_le_of_isTPP`
connects TPP triples to tensor-rank bounds.

### Xlib sorry chain

**Sorry-free** (relevant to ω):
- `TPP.lean` — `TripleProductProperty`, `tppCapacity`, abelian
  barrier |S||T||U| ≤ |G|
- `Wedderburn.lean` — block-size uniqueness
- `CharDegrees.lean` — `charDegrees`, Σd² = |G|, #irreps =
  #conjugacy classes
- `FourierBarrier.lean` — `master_bound`: nonabelian Fourier,
  Parseval, Gowers-trick bound
- `BCGPUBarrier.lean` — six barrier statements (n(G) barrier,
  normalizer barrier, center barrier)

**Sorry-bearing** (honest skeletons):
- `CUCapacity.lean` — **1 sorry**: `capacity_rpow_le_charDegreeSumReal`
  (CU Theorem 4.1: β(G)^{ω/3} ≤ D_ω(G)). Also 3 axioms:
  `matrixExponent`, `two_le_matrixExponent`,
  `matrixExponent_le_three`.
- `STPPWreath.lean` — **6 sorrys**: STPP capacity inequality,
  wreath char-degree bound, STPP-to-TPP lift, wreath
  pseudo-exponent bounds, amplification limit α(Gₙ) → 2.

**Dependency order to close all sorrys:**
`BilinearComplexity.Omega` (replace 3 axioms in CUCapacity)
→ CU Theorem 4.1 (needs tensor rank + group-algebra embedding
+ BCS 15.1/15.5, partially covered by GroupTensor.lean)
→ STPP capacity (needs Schönhage ASI)
→ wreath char-degree bound (needs Clifford theory)
→ wreath pseudo-exponent → amplification limit.

### Known debt

1. **ω duplication** (mechanical fix): `omega` in `Omega.lean`
   (honest sInf) vs `matrixExponent` in `CUCapacity.lean`
   (axiom). Replace 3 axioms with imports from
   `Proofs.BilinearComplexity.Omega`. This is a refactor,
   not a foundation.
2. **Asymptotic rank R̃(T)**: not defined. Needed for every
   wall/barrier statement. Fekete + existing Kronecker
   submultiplicativity should make this cheap.
3. **Field-independence of ω**: not proved.
4. **Tensor3 vs Tensor**: `Vp2.Tensor3 k n` (cubic) and
   `BilinearComplexity.Tensor k a b c` (rectangular) are
   deliberately separate. No unification planned.
5. **TPP docstring**: misattributes left form. One-line fix.
6. **`Matrix.trace_comp`**: proved locally in CyclicBlock.lean,
   upstreamable to Mathlib.

---

## Thread 3: the group sieve

Systematic screening of nonabelian groups ≤ 511 for TPP
capacity, using Murthy/BCGPU bounds as a cascade. Novel as
a method — no precedent for per-group screening in the
literature.

### Current state

- 89.8% survive to Tier 2b (packing ceilings only)
- 5.2% hard-rejected, 5.1% capped
- Order-256 stratum is the largest uncovered gap
- No survivor shown to do anything — ceilings are upper bounds

### Programs in `Scratch/GroupSieve/`

- `groupsieve.sage` (50k lines) — main cascade
- `census.sage` (13k) — survivor census
- `rho0.sage` (35k) — exact ρ₀ computation (4–8h run)
- `tier4.sage` (12k) — Tier 4 ranking (~50 min)
- `gelfand.sage` (17k) — Gelfand-pair extension
- `lemma_sweep.sage` (21k) — lemma sweep

### Forge-grade program deliverables

The next orchestrator should produce **forge-grade** versions
of the sieve programs, targeting the user's forge
infrastructure (up to 256 vCPU, 512–1024 GiB memory).

Requirements for forge-grade programs:
- Each program has two modes: a **toy mode** (runs in seconds
  on a laptop, exercises the full pipeline on a tiny slice —
  e.g. groups of order ≤ 24) and a **full mode** (designed
  for the forge, exploits all available parallelism)
- Stated space size and projected runtime for full mode
- Checkpoint/resume support
- Progress reporting (stdout, parseable)
- Sharded output (JSONL)
- Well-reviewed: no silent failures, no edge-case crashes
  at scale
- The deliverable is a complete, inspectable program plus
  the exact run command — not agent-run output

The existing `Scratch/GroupSieve/` programs are prototypes.
The forge-grade versions should be rewritten from them, not
patched. Confirm scope with the user before starting.

### Pf3 connection

If Pf3 (abelian direct factor) resolves, Im6 wires the
result into the sieve as a new tier. A proof gives a
product-decomposition rejection tier; a counterexample
gives a must-not-reject anchor.

---

## What NOT to do

- Do not autonomously dispatch provers or create task cards
  without confirming direction with the user.
- Do not run `lake build` without the flock lock.
- Do not modify `Manuscripts/` (read-only).
- Do not commit (only the user or an explicit orchestrator
  instruction commits).
- Do not run sieve computations yourself — produce programs
  for the user's forge. `timeout 60 sage -c` probes are fine
  for single-fact checks.
- Do not trust training data on mathematical claims. Ground
  everything in `sage`, `wiki`, `oeis`, `erdos`, or primary
  sources.
