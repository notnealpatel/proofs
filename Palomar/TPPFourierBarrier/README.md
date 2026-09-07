# TPP Fourier barrier

## Candidate claim

This candidate formalizes the finite-group Fourier barrier of Blasiak–Church–Cohn–Grochow–Umans (BCGPU), Theorem 3.2 (`thm:gowerstrick`, arXiv:2204.03826).

For a finite nonabelian group $G$, with
`nG G := (GroupTPP.CharDegrees.minNontrivIrrepDim G : ℝ)`, every finset triple $S,T,U$ satisfying `TripleProductProperty S T U` obeys

$$
|S||T||U| \le \frac{|G|^{3/2}}{\sqrt{n(G)}}+|G|.
$$

The exact Lean declaration is `GroupTPP.BCGPUBarrier.bcgpu_thm_3_2`. Its hypotheses are `[Group G]`, `[Fintype G]`, `[DecidableEq G]`, an explicit noncommutativity witness `∃ a b : G, a * b ≠ b * a`, and a TPP hypothesis. Empty sets are handled by the theorem itself.

## Formal content

The analytic core is `GroupTPP.FourierBarrier.master_bound`. It applies to an indexed algebra equivalence

```text
e : ℂ[G] ≃ₐ[ℂ] (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
```

with `[∀ i, NeZero (d i)]`, a unitary decomposition `IsUnitary e`, an integer `n ≥ 2`, and the lower-bound condition `1 < d i → n ≤ d i`. For nonempty TPP triples it yields the same inequality with $n$ in place of $n(G)$.

The supporting declarations are:

- `ind`, `indInv`, and `gowersElt`: indicator elements and the six-fold Gowers convolution.
- `gowersElt_apply_one`: under TPP, the identity coefficient is $|S||T||U|$.
- `inversion`: Fourier inversion via the trace of left multiplication.
- `exists_isUnitary`: blockwise conjugation to a unitary Wedderburn decomposition.
- `parseval_norm_sum`: the weighted Frobenius-norm Parseval identity.
- `trace_gowersElt_one_dim`: nonnegativity of one-dimensional Gowers blocks.
- `exists_trivial_block`: existence of the trivial one-dimensional block.
- `exists_one_lt_dim_of_nonabelian`: a nonabelian group has a block of dimension greater than one.

The BCGPU bridge uses `two_le_minNontrivIrrepDim` and the character-degree comparison `charDegrees_eq_of_algEquiv` to instantiate `master_bound` with `n := minNontrivIrrepDim G`.

## Contribution and attribution

This is a formalization of known mathematics, not a new barrier theorem. The repository attributes the result to BCGPU, *Matrix multiplication via matrix groups*. The formal contribution is the Lean development of the Gowers/Fourier, unitarization, Parseval, and character-degree bridge needed for the finite inequality.

`bcgpu_cor_3_3` and `bcgpu_cor_3_4_kernel` record finite consequences under the additional hypothesis $|G|^\delta \le n(G)$. The asymptotic statement about families of groups, and any conclusion about the matrix-multiplication exponent $\omega$, requires extra family hypotheses and is not asserted here.

## Recovered evidence and limitations

The principal source locations are `Proofs/GroupTPP/FourierBarrier.lean:54–63, 124, 386, 468, 519, 668, 699, 733, 901, 941` and `Proofs/GroupTPP/BCGPUBarrier.lean:86, 100, 146, 209, 260`. `Proofs/GroupTPP/CUCapacity.lean` separately formalizes the Cohn–Umans capacity bound and $\omega$-related statements; it is context, not an additional premise of this candidate. `Documents/exotic-groups-for-mm.md` contains planning language and conjectural screening implications, not evidence that a suitable matrix-multiplication group exists.

This recovery did not run Lean, a build, tests, or an axiom/proof audit. The source declarations were inspected, but compilation and dependency status remain unverified in this recovery.

## Next obligations

An authorized prover/package pass should type-check the selected theorem and inspect its dependency and axiom footprints in the pinned environment. A later Palomar package would still need the independently scoped Challenge, Solution bridge, comparator configuration, and `formalization.yaml`, with imports checked against the current allowlist. Human review remains pending; no acceptance, priority, or approval is claimed.
