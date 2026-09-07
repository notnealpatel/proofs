# Integer complexity of powers of three

## Candidate summary

This candidate isolates a classical exact result for Mahler–Popken integer complexity, for an audience in elementary number theory and formalized mathematics. It is a **formalization of known mathematics**, not a claim of a new theorem or global priority. The intended result is that the canonical product of copies of `1 + 1 + 1` is optimal for every positive power of three.

## Exact formal object and result

The definition layer is `Proofs/NumberComplexity/IntComplexity.lean`. In namespace `NumberComplexity`, `Expr` is the inductive language with constructors `one`, `add`, and `mul`; `Expr.eval` evaluates a term in `ℕ`, and `Expr.cost` counts its `one` leaves. The noncomputable definition

```lean
complexity (n : ℕ) : ℕ :=
  ⨅ e : {e : Expr // e.eval = n}, e.1.cost
```

is the least cost of a `{1,+,×}` expression for `n`. The index subtype is empty at zero, so `complexity_zero : complexity 0 = 0` is a documented junk-value convention, not a representation of zero. The order API includes `complexity_le_cost`, attainment `exists_cost_eq_complexity` for `1 ≤ n`, `le_complexity`, `one_le_complexity`, `complexity_le_self`, `complexity_one`, and additive/multiplicative subadditivity. Every substantive statement here keeps its positivity guard.

The powers-of-three development is in `Proofs/NumberComplexity/DoublingConjecture.lean`, importing that definition layer. Its central declaration is exactly

```lean
theorem complexity_three_pow {b : ℕ} (hb : 1 ≤ b) :
  complexity (3 ^ b) = 3 * b
```

The domain is `b : ℕ` with `1 ≤ b`; `b = 0` is deliberately excluded because `3^0 = 1`, `complexity 1 = 1`, whereas `3 * 0 = 0`. The witness `Expr.threePowSucc` is the product of `b + 1` copies of `1 + (1 + 1)`, with declarations `eval_threePowSucc` and `cost_threePowSucc` proving value `3^(b+1)` and cost `3*(b+1)`.

The lower-bound chain is explicit: `Expr.pow_three_eval_le_three_pow_cost` proves `e.eval^3 ≤ 3^e.cost` for every expression, and `pow_three_le_three_pow_complexity` gives `n^3 ≤ 3^complexity n` for `1 ≤ n`. The analytic restatement is `three_mul_logb_three_le_complexity`, namely `3 * Real.logb 3 n ≤ (complexity n : ℝ)`. At `n = 3^b`, the cube inequality is tight, so it yields the matching lower bound `3b`; the canonical witness supplies the upper bound.

## Attribution and contribution

The source records OEIS A005245 as the Mahler–Popken complexity sequence. Iraids, Balodis, Čerņenoks, Opmanis, Opmanis, and Podnieks, *Integer complexity: experimental and analytical results*, arXiv:1203.6462, Theorem `cbounds2`, states the corresponding classical base-three result (and an iff characterization). The local source also records the two-sided bound as known from Selfridge and Coppersmith, with Iraids reporting Guy’s attribution to Dan Coppersmith; Altman–Zelinsky (arXiv:1207.4841) specifically credit Selfridge with the lower bound. This README preserves those attributions without assigning global novelty. The formal contribution is a repo-level Lean encoding of the definition, the classical cube lower bound, and the sharp base-three specialization. The iff statement and the literature’s parenthetical comparison/shortest-representation claim are not asserted as separate formal declarations here.

## Recovered evidence, limitations, and obligations

Evidence recovered for this README is the two source files above and `Documents/mathlib-integer-complexity/PROPOSAL.md`, whose proposed API separately places the definition and bounds layers. The source contains an axiom-print block, but this recovery did not run Lean, inspect generated declarations, or perform a proof audit. The local proposal itself marks its prior compile report as unverified. No fresh literature or prior-formalization search was performed; consequently there is no priority claim. The current `DoublingConjecture.lean` also contains an unrelated intended open powers-of-two `sorry`; a Palomar Solution must isolate the base-three declarations and demonstrate that no compared theorem depends on `sorryAx`.

Before any submission, a prover must prepare an independent small Challenge and a sorry-free Solution with matching names and types, preserving the guards and attribution. A package maintainer must provide the pinned project manifest/toolchain, allowlisted Challenge imports, Comparator configuration, and `formalization.yaml` describing this as source-based formalization, AI assistance, pending human review, and the stated gaps. Lean and Comparator verification, including the permitted-axiom audit, must then be run and recorded; none is claimed here. This workspace intentionally contains only this README, so the candidate is not acceptance- or registry-ready.
