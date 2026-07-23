# T5 — Addition chains: the bridge `min shears for xⁿ = l(n)`, and the open conjectures

**Provenance.** Surfaced while grounding T2 ("how hard is inversion?"): computing a
single power `xⁿ` with only multiplications = **shortest addition chain** `l(n)` =
OEIS **A003313**. Mining that neighborhood hit **A230528** with a 2024 open comment.
(Numeric details below are **scan-reported** — reconfirm against OEIS/Wikipedia
before relying on them.)

## The on-thread, worth-doing piece: the bridge lemma

**Novelty.** Novel *as formalization* (addition chains / multiplicative complexity
absent from Mathlib); math is Knuth TAOCP 4.6.3.

Statement (informal): the minimum number of shear multiply-adds to produce `xⁿ` in a
register **= `l(n)`** (shortest addition-chain length). One shear fed registers
`xⁱ, xʲ` yields `x^{i+j}` — i.e. **one shear = one addition-chain step**.

- **Lower bound** `≥ l(n)`: clean multiplicative-complexity statement.
- **Upper bound** `= l(n)`: achievable, *allowing garbage powers* in other registers.
- **Clean-scratch** (ancilla→0) adds Bennett uncompute (~2×) — state carefully;
  don't conflate "produce xⁿ" with "produce xⁿ and clear all scratch".

**Payoff:** sharpens T2 from the crude `⌈log₂(p−2)⌉=256` floor to the *exact*
`l(p−2)` (a specific integer ≈ 265–285; best-known chains, not proven optimal).

Formalize: define `AdditionChain`/`chainLength : ℕ → ℕ`, relate to `xⁿ`
computation. Also connect to `A014701 = ⌊log₂ n⌋ + popcount n − 1` (binary method
upper bound, closed form, **solved**).

## The open conjectures — context/motivation, NOT session targets

| Item | Statement | Status | Verdict |
|---|---|---|---|
| Scholz–Brauer | `l(2ⁿ−1) ≤ n−1+l(n)` | OPEN (verified ~5.78M) | **hopeless to prove; computation-saturated.** Skip. |
| A230528 gap>1 | `∃ k, l(k)−l(2k) ≥ 2`? (all 7 known terms have gap 1; smallest term `375,494,703`) | OPEN, both directions | **lottery ticket:** exact `l(n)` is search-hard; gap-2 (if it exists) presumably far larger. Bounded Go search only. |
| secp256k1 chain | exact `l(p−2)` / optimal chain | best-known ≠ proven | on-thread but proving optimality of a 256-bit exponent is search-hard |

Relevant OEIS/refs: A003313 (l(n)), A230528, A014701 (binary method, solved),
A005766 (min-cost chains, recurrence known), Brian Smith ECC inversion-chain
catalog, Scholz conjecture (Wikipedia).

## Decisions for USER before committing

1. Commit only the **bridge lemma** (on-thread, novel-in-Mathlib, sharpens T2), and
   treat the conjectures as motivation? (Recommended.)
2. If any computational bet: a **Go** search (bit-packed, exact-`l(n)` via IDA*/
   branch-and-bound) for (a) A230528 gap-2, or (b) improving/verifying the
   secp256k1 `p−2` chain. Both are pivots off the formalization thread — pursue only
   if the USER explicitly wants a combinatorics detour.
3. Skip Scholz–Brauer entirely (agreed hopeless)?
