# Shear addition chains

## Candidate result

This candidate formalizes an exact correspondence between shortest addition chains and a restricted reversible multiplication-register model. The principal source is `Proofs/ShearEC/ShearAdditionChain.lean`; it imports `Proofs/NumberComplexity/AdditionChain.lean`. `Proofs/ShearEC/ShearAdditionChains.lean` is only import scaffolding and is not theorem evidence.

`MonomialShearProgram : List ℕ → Type` is indexed by a newest-register-first exponent list. Its constructor `input` supplies the single register `[1]`, representing `x`. A `shear` chooses two existing registers and allocates a fresh target whose exponent is their sum. All older registers are retained. Thus a program records source indices as data, not merely an existential claim. `MonomialShearProgram.shearCount` counts these fresh-target multiplication shears.

The supporting development defines `NumberComplexity.IsAddChain`, `chainSteps c := c.tail.length`, `AdditionChain n := {c : List ℕ // IsAddChain c ∧ c.head? = some n}`, and the noncomputable shortest-chain function

```text
l n := ⨅ c : AdditionChain n, chainSteps c.val.
```

The central declaration is:

```text
theorem minimumMonomialShears_eq_l (n : ℕ) (hn : n ≠ 0) :
  minimumMonomialShears n = l n
```

Here `MonomialShearComputation n` packages an exponent trace, a `MonomialShearProgram`, and the condition that its newest exponent is `n`; `minimumMonomialShears` is the infimum of the corresponding `shearCount`s. The bridge is supported by `MonomialShearProgram.isAddChain`, `shearCount_eq_chainSteps`, and `nonempty_monomialShearProgram_iff_isAddChain`. `exists_optimal_shear_circuit_realization` additionally compiles an optimal program to a shear-only `ShearCircuit.Circuit`, with count `l n` and every register equal to the corresponding power of `x` over any commutative semiring.

At `n = 0`, both infima have the documented value `0` because their indexing types are empty. The declaration `minimumMonomialShears_eq_l_all_with_empty_infimum_at_zero` records this bookkeeping equality, not an operational computation. The substantive theorem is the positive-exponent statement above.

## Contribution and context

The addition-chain function is established mathematics: the supporting file identifies OEIS A003313 and cites Knuth, *The Art of Computer Programming*, §4.6.3. This project’s contribution is a formal, source-indexed bridge to a fresh-target monomial shear model, together with an operational circuit realization. It should interest researchers in addition chains, formalized arithmetic complexity, reversible or quantum arithmetic, and elliptic-curve circuit design. This is best described as a new formalization/model correspondence, not a claim of new addition-chain mathematics. No global novelty or priority claim is made. A prior-formalization relationship has not been established in this recovery and remains open.

## Fidelity limits and recovered evidence

The equality applies only to one input register containing `x`; counted operations multiply two existing monomial registers into a fresh zero target; old registers remain available as permitted garbage; and no free affine mixing occurs in this model. It does not identify `l n` with the minimum over the broader `ShearCircuit.Circuit` language, does not require clean scratch registers, and does not claim an unrestricted inversion or full elliptic-curve point-addition optimum. In particular, any surrounding EC or inversion results must not be read as an exact unrestricted addition-chain lower bound.

This README records recovered source declarations and saved scout/policy evidence, not a fresh proof audit. No compilation, Lean elaboration, test run, or axiom audit was performed here. An inherited direct-file check reported an import-path failure for `NumberComplexity`; package-target verification remains a required obligation. No agent review is required for this recovery; human review is pending.

## Attribution and next obligations

The repository’s `LICENSE` is present, but the intended Palomar attribution and responsible human maintainer have not been established here. AI assistance was used to recover this candidate README; no AI authorship, human approval, Palomar acceptance, registration, or endorsement is claimed. Before any submission, a prover should verify the package-targeted imports and principal declarations, review semantic alignment and axioms, and prepare the required independent Challenge/Solution and metadata. Those artifacts are intentionally not created here.
