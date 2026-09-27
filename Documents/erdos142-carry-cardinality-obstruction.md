# Carry-cardinality obstruction

**Kernel checked.** At revision
`37a2ec6468a5a33ee7e3dd966ecc816d0971f46c`,
[`Proofs/Erdos/Erdos142/CarryCardinalityCapObstruction.lean`](../Proofs/Erdos/Erdos142/CarryCardinalityCapObstruction.lean), imported by `Proofs/Erdos.lean`, proves the finite endpoint
`Erdos142.exists_carryCardinalityCap`. The focused module and full `Erdos` build succeeded (8813 jobs). Independent vacuity and foundations reviews were clean. The public endpoints use exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

For every `N ≥ 3`, the theorem supplies a bounded `G ⊆ [0,N) × [0,N)` and a common in-range row/column size `b` such that:

- every ordinary `ℕ` row and column fiber is 3-AP-free (including the empty fibers at out-of-range indices);
- all `N` in-range rows and columns have size `b`, with `2b ≤ N`;
- `N · rothNumberNat N ≤ 2 · |G|`;
- `(0,0), (1,1), (2,2) ∈ G`; and
- the base-`N` scalar image `{xN+y : (x,y)∈G}` contains `{0, N+1, 2(N+1)}`, a nontrivial scalar 3-AP.

The scalar encoding is injective on the bounded square, but this witness is deliberately **not** scalar-3-AP-free: the diagonal gives the displayed progression.

## Finite construction

Start with a maximum ordinary 3-AP-free set `C ⊆ [0,N)`, of size `r=rothNumberNat N`. Split it between the lower interval of length `⌊N/2⌋` and the upper interval. One piece contains at least half of `C`; translate the upper piece down when needed. This gives an ordinary 3-AP-free set in an interval of length `⌈N/2⌉`, with at least `r/2` elements. Shrink it if necessary to size at most `⌊N/2⌋`, retaining the half-size lower bound. Its representatives are short enough that a modular 3-AP in `ZMod N` would lift to an ordinary one. Translate the resulting modular cap `B` so that `0∈B`; it satisfies `2|B|≤N` and `r≤2|B|`.

Take the difference graph
`G = {(x,y) : x,y<N, x−y∈B mod N}`. Every row and column is a translate or reflection of `B`, lifted to its natural representatives, so its ordinary fiber is 3-AP-free and has size `b=|B|`. Counting rows gives `|G|=N|B|`, hence `N r≤2|G|`. Since `0∈B`, the diagonal points lie in `G`; their scalar images are `i(N+1)` for `i=0,1,2`.

## Scope and consequence

This is a finite, kernel-checked obstruction, not an asymptotic estimate for `r(N)`, not a scalar progression-free construction, and not a solution of Erdős problem 142. It shows that the relaxation using only ordinary row/column freeness and the pairwise fiber-size cap cannot imply any universal `o(N r(N))` cardinality upper bound: its allowed instances already have size at least `N r(N)/2`. Consequently that relaxation alone cannot prove the desired P-shaped saving. Stronger information—particularly control of scalar carries—is necessary.

## Closed computational lead

Exhaustive and sampled tests suggested a target-wise union-reflection coverage inequality that would imply

\[
 r(N^2)\le N+\sqrt N\,r(N)^{3/2}.
\]

**Exploratory or conditional; closed dead lead.** This is not a live conjecture or an accepted computational theorem. The accepted Behrend lower bound absorbs the additive `N` eventually, turning the proposed inequality into an eventual P-shaped estimate with exponent `η=1/2`:
\[
 r(N^2)\le C N^{1/2}r(N)^{3/2}.
\]
But `1/2>\sqrt2-1`, and the accepted square-scale negative-defect theorem rules out this eventual estimate. Indeed, it would force
`X(N)=log(r(N)^2/r(N^2)) ≥ -\tfrac12\lambda(N)-O(1)`
for all sufficiently large `N`, whereas on fixed square towers the kernel-checked theorem gives, frequently,
`X(N)≤-(2-\sqrt2-\varepsilon)\lambda(N)`; choose `\varepsilon` with `2-\sqrt2-\varepsilon>1/2`. Thus finite tests cannot support this inequality asymptotically. A viable positional/collision route must retain reflected-digit locations and target an exponent `η≤\sqrt2-1`.
