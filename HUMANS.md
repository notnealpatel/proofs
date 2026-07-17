Reconcile this generated text with the rest
of the document in order to re-write something
relevant to me.

```
Read all four. Verdict per card — none is wrong, so this is a focus call, not a correctness call:

Pf3 (abelian direct factor: ρ₀(A×G) = ρ₀(G)) — KEEP. The strongest card of the four. The ≤ direction is verified-open (flash sweep across 8 sources found it stated nowhere) — a genuinely novel statement whose proof or counterexample both pay: it's the sieve's missing product-decomposition tier and closes the known [24,10]/[24,11] cascade gap. Novelty sweep and proof skeleton are sunk work living only in this card; its three resets were infrastructure crashes, not math failures — zero evidence it's stuck.

Im6 (product decomposition tier) — KEEP IFF Pf3 KEPT. It's Pf3's payoff wiring, correctly gated on either outcome (proof → tier, counterexample → harness anchor). Meaningless without Pf3; deleting Pf3 but keeping Im6 would be incoherent. They live or die as a pair.

Ep542 (Schinzel–Szekeres 31/30) — KEEP, or shelve if the Erdos track is closed. Two facts: (1) it's the direct implementation of your own data/NOTES.md directive ("formalize at least 2 more proven Erdos problems… extract the time for the ledger"); (2) the card embeds a planner-probe-verified proof architecture — exact weight system, the 0.016-margin danger zone, the 2^62 trap in the stretch goal — that would be expensive to reconstruct. If the ledger/benchmark goal still stands, keep. If your focus has fully moved to the ω program, shelve, don't remove — deletion burns the prep.

Pf4 (dihedral subset ρ ≤ 4/3) — SHELVE. Real open math (USER-decided OPEN despite the private-communication rumor) and a first-published-proof opportunity — but it's the lowest-relevance of the four to both your ω=2 interest and the sieve: dihedral groups move nothing asymptotically, and the Kneser-engine attack is the highest-variance prover sink on the board. Shelving preserves the completed novelty sweep and plan skeleton; wiring it back later is one edge.

Net: remove nothing outright. Keep Pf3+Im6, keep Ep542 (your call on ledger-track status), shelve Pf4. If you confirm, the commands are goof tasks shelve Pf4 (and optionally Ep542) — say the word and I'll run them, or run them yourself if you prefer.
```

# HUMANS.md — frontier accounting

Written by the `o46max-4` orchestrator session, 2026-07-12 ~21:30 UTC.
For Nool to read, edit, and strike through. Numbers in [brackets] are
notability 0–3. "grep-clean" means no `sorry` by grep; **no `lake build`
has been run by this session** (agents hold the build lock), so every
claim below is statement-level until a clean build confirms.

## kernel-solid (previous waves, build-verified by their campaigns)

- `rank(flattening ⟨n,n,n⟩) = n²` exact, any nontrivial CommRing.
  Pillar 1a of the four-way chain, machine-checked. [3]
- `R⟨2,2,2⟩ ≤ 7` as a kernel-`decide` rank statement, ℤ and ℚ. [2]
- Rank calculus over CommSemiring: ⊕-subadditive, ⊗-submultiplicative,
  cyclic, GL-invariant, reindex. [2]
- TPP left/right fork: not equivalent on the same triple (kernel
  counterexample, D₃); inversion bridge proved; all capacity numbers
  convention-independent. Left form was our own transcription mutation,
  not a literature convention. Docstring correction still pending. [1]
- Blasiak–Cohn ITCS 2023 packing-bound sentence is false under their own
  Def 2.1; 90 Sage counterexamples on S₃; repaired by CU 2003's own
  `x⁻¹y` phrasing; their theorem unaffected. Erratum-grade. [2]
- β(D₁₂) = 16 kernel-checked, agrees with Hedtke–Murthy Table 1. [1]

## landed in the last ~3h (grep-clean, UNAUDITED — statements not yet read by a human or frontier agent)

- `BilinearComplexity/Omega.lean` — ω := sInf over rank exponents;
  `two_le_omega`, `omega_le_three`, `omega_lt_three`,
  `omega_le_logb_two_seven : ω ≤ log₂ 7`. [3 if statements are right]
- `BilinearComplexity/Winograd.lean` —
  `rank_matMulTensor_eq_seven : rank (matMulTensor ℤ 2 2 2) = 7`.
  Lower bound via ZMod 2 + `decide`, lifted to ℤ. Field-general version
  (char ≠ 2) not claimed. [3 if statements are right]
- `BilinearComplexity/KroneckerMatMul.lean` — the kron/matMul compat
  lemma (the deferred prerequisite for everything asymptotic). [2]
- `BilinearComplexity/MatMulMono.lean` — padding monotonicity. [1]
- `BilinearComplexity/SliceRank.lean` — slice rank, ≤ rank, ambient
  caps, cyclic invariance, Tao's diagonal lemma with full counting
  argument. The BCCGNSU/wall engine. [2]
- `BilinearComplexity/GroupTensor.lean` — matmul-in-group-algebra
  embedding (the bridge the sieve's ω-relevance runs through). [2]
- `Xlib/FourierBarrier.lean` (~1200 lines) — nonabelian Fourier over
  MonoidAlgebra ℂ G, Wedderburn blocks, Parseval, `master_bound`.
  Claims a character-degree-weighted packing bound under TPP. [?]
- `Xlib/BCGPUBarrier.lean` — claims six barrier statements proved. [?]
- `Xlib/CUCapacity.lean` — CU Theorem 4.1 formally STATED, honest
  sorry-skeleton. Two declared debts: (1) Thm 4.1 proof itself,
  (2) `charDegrees` indexed-Wedderburn enumeration. [2 as statement]

## known rot / unification debt

- ω exists twice: honest `sInf` def in `Omega.lean` vs axiomatized
  `matrixExponent` constant in `CUCapacity.lean`. Must be unified or
  the Xlib ω-statements are about an undefined symbol. This is the
  definitional-adequacy failure mode one layer up. NEEDS A CARD.
- `TripleProductProperty` docstring still misattributes the left form
  to Murthy/Wikipedia. One-line fix, no proof churn.
- Roadmap still claims "no tensor rank in Mathlib" — false, Holor.cprank
  (Bentkamp 2018). Fix before anything is cited externally.

## genuinely missing (nothing in flight touches these)

- Asymptotic rank R̃(T) = lim R(T^⊗k)^{1/k} (Fekete). Every §4 wall
  statement in Drafts/four-way-chain.md quantifies over R̃; without it
  no wall statement can be written in Lean, ever.
- The wall meta-theorem (`asymptotic_silence`): any all-sizes c·n²
  lower-bound family regularizes to exactly n². Cheap once R̃ exists;
  would be the first machine-checked barrier-shaped statement in
  algebraic complexity.
- Field-independence of ω (ω depends only on char k) — the cheapest
  real answer to "does this apply to all classes of matmul". Circuits
  adequacy (Strassen '73) consciously skipped; wording must say
  "rank exponent" until then.

## decisions only Nool can make

1. Send the Blasiak–Cohn erratum email? Two paragraphs + Sage script +
   Lean counterexample. Everything else about it is settled.
2. Authorize the statement-level audit of the three danger files
   (Winograd RankLE encoding, FourierBarrier.master_bound, BCGPU
   statements). Highest-value frontier attention on the board;
   read-only, doesn't touch the build.
3. ω/matrixExponent unification card — cut it now or after this wave
   settles?
4. Paper posture — parked per your instruction until the work is
   clear to you. (For later: R⟨2,2,2⟩=7 + ω ≤ log₂7 + slice rank +
   CU 4.1 stated is already past the bar both analysis docs set.)

## 20-minute personal verification recipe

The definitions are the attack surface; the kernel does the rest.

- Read: `BilinearComplexity/Basic.lean` — `Tensor`, `RankLE`, `rank`,
  `matMulTensor` (~60 lines). If these say what they should, every
  theorem above means what it claims.
- Read: `Omega.lean:51` (`omegaSet`) and `SliceRank.lean:82`
  (`SliceRankLE`).
- Read: `Xlib/TPP.lean:649` (the decide counterexample) and the two
  TPP defs above it.
- Run (after agents release the lock):

```
cd ~/p/proofs/Proofs && flock .lake/agent.lock lake build
```

- Then axiom-audit the headliners in Scratch.lean:

```
#print axioms Proofs.BilinearComplexity.rank_matMulTensor_eq_seven
#print axioms Proofs.BilinearComplexity.omega_le_logb_two_seven
#print axioms Proofs.BilinearComplexity.sliceRank_diag
```

Expect `[propext, Classical.choice, Quot.sound]` and nothing else.
Anything with `sorryAx` or `matrixExponent` in the list is conditional.

## sieve status (unchanged this session)

Checkpoint dataset is a validated screening instrument, not a
discovery: 89.8% of nonabelian G ≤ 511 survive to Tier 2b, order-256
stratum still open, Tier 4 ranking not run. No survivor shown to do
anything yet. See data/NOTES.md `f5high-1` block.
