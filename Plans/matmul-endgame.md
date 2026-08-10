# matmul-endgame — finishing the machine-checked Cohn-Umans wreath development

The critical path to a sorry-free GroupTPP formalization of
CKSU's theorem:asi for general finite groups, via the wreath
product amplification route.  Close the three remaining
sorries, land the Clifford theory infrastructure, and finish
the capacity chain.

Sources: `git show 4901d3b:Plans/STATE3.md` sections binding
specs, live cards (matmul rows only), critical chain, and
dropped-conjecture record; `git show 4901d3b:Plans/STATE5.md`
sections stpp_capacity resolution options, same-name hazards,
wreathGamma misstatement, rejected routes, and known-hard
targets; reorganized 2026-08-10.

## sorry inventory

Three sorries remain (full inventory in Plans/debt.md):

- `Proofs/GroupTPP/STPPWreath.lean:389` — `stpp_capacity_le`
- `Proofs/GroupTPP/STPPWreath.lean:939` — `stpp_capacity_le_of_wreath`
- `Proofs/BilinearComplexity/PeelingSupport.lean:498` — `cover_outmass_even`

## critical chain

Cv1+Mn1 -> Hu18 -> Cl1 -> Cl2 -> Cl3 -> Cl4 -> Cl5 -> Fi1 -> Hu19

Nine nodes.  Cv1 (FDRep-charDegrees bridge pricing) and Mn1
(multinomial assembly closure) are the dispatchable roots;
Hu18 is the mid-campaign re-gate (confirm Clifford spend
~3-8k lines + irrep-indexing choice Q2); Cl1-Cl4 are the
Clifford theory prover cards; Cl5 restores `[Group H]` on
`wreath_charDegree_bound`; Fi1 instantiates and closes
:385/:389 sorry-free; Hu19 is the reporting gate.

Side chains: Im16 -> Hu11 and Im16 -> Im17 -> Hu12.
Frozen branches: Hu15 -> Pl28, Hu16 -> Pl23, Hu17 -> Pl26.
Tb1 gates Pl28 only through Hu15's conditions, not a DAG edge.

Cheapest-first ordering per the critiques: Ng1 ("cheapest
positive-value item on the whole board"), then Mn1 + Cv1
in parallel, then the Hu18 decision.

## live cards (matmul only)

| card | agent | deps | goal |
|------|-------|------|------|
| Mn1 | postdoc | (Pl21) | close `stpp_capacity_le_of_wreath` :939, relax `[CommGroup G]` -> `[Group G]`; conclusion frozen |
| Cv1 | consumer | (Pl21) | price FDRep<->charDegrees bridges; deliver `mathlib-clifford-coverage-v2`; feeds Hu18 Q2 |
| Ng1 | postdoc | (Pl22, Ad1) | WreathNg cleanup: unpin F3 suspect, irrep->charDegrees bridge, BCGPU barrier corollary |
| Tb1 | postdoc | (Pl22, Ad1) | new `BilinearComplexity/STPPBarrierStatements.lean`: TricoloredSumFree, K-TCSF kernel, statements only |
| Pd1 | postdoc | (Im14, Im15) | K8 untwistable-member bound: test-first against new data, then prove or record obstruction |
| Im6 | implementer | (Pf3, Im2) | encode the Pf3 refutation as MUST-NOT-REJECT sieve anchor (counterexample branch) |
| Im16 | implementer | (Im15) | materialize metered sweep programs for PSL(2,17)/S_7/A_8; pricing input for Hu11; do not run |
| Im17 | implementer | Im16 | PSL(2,27) p=3 hunt phase-1 screen; verdict HUNT-LIVE/DEAD/COLD for Hu12 |
| Hu9 | human | (Ma1) | sign off `abelian-factor-refutation` for circulation; terminal node, active |

Hu9 (manuscript circulation sign-off) is a USER adjudication gate, zero-cost; the manuscript it gates is committed. (Source: STATE3 adjudication items, lines 325-337.)
| Hu11 | human | (Im15), Im16 | metered gate: approve wave-2 sweeps PSL(2,17)/S_7/A_8 |
| Hu12 | human | Im17 | metered gate: approve PSL(2,27) phase-2 exact beta_0 (~2.5-3 h export) |
| Hu15 | human | (Pl22) | gate Pl28 on: Tb1/B1 landed sorry-free AND J(q) priced and accepted; active |
| Hu16 | human | (Hu13) | revive-or-kill Pl23 remnant; recorded verdict 2026-07-29: KEEP PARKED |
| Hu17 | human | (Hu13) | Programs/ audit gate before Pl26; recorded verdict 2026-07-29: KEEP PARKED |
| Hu18 | human | Mn1, Cv1 | mid-campaign re-gate: confirm Clifford spend (~3-8k lines) + irrep-indexing choice (Q2) |
| Hu19 | human | Fi1 | shape-2 reporting gate: "CKSU theorem:asi in Lean for general finite groups" headline |
| Cl1 | prover | Hu18 | induced-rep dimension formula `dim Ind = [G:K]*dim V` in new `GroupTPP/InducedDimension.lean` |
| Cl2 | prover | Cl1 | irrep-indexing layer, `Irr(H^n) = Irr(H)^n`, S_n orbits; highest-risk card |
| Cl3 | prover | Cl2 | Young-subgroup extension + induced-degree formula; heaviest wave (1500-3500 lines) |
| Cl4 | prover | Cl3 | irreducibility + exhaustion via sum-of-squares; charDegrees multiset identity |
| Cl5 | postdoc | Cl4 | restore `[Group H]` on `wreath_charDegree_bound` (:510); abelian proof -> `_of_comm` |
| Fi1 | postdoc | Cl5 | close :385/:389 by instantiation; trust sweep; GroupTPP sorry-free |
| Pl23 | planner | Hu16 | post-sweep triage remnant (frozen; salvage residue listed below) |
| Pl26 | planner | Hu17 | chow_sm3: pin exact small Chow ranks over F_2 for tr(X^3) and det(X) (frozen) |
| Pl28 | planner | Hu15 | plan BCCGNSU Theorem B (slice-rank barrier) formalization vs `SimultaneousTPP` |

Non-matmul live cards stay out; reference Plans/erdos.md and
Plans/conjecture-hunts.md as appropriate.

## binding spec: Mn1 (multinomial assembly blocker)

Live card Mn1: the remaining sorry in
`stpp_capacity_le_of_wreath` (`stpp_capacity_le_comm`
derives from it).

CKSU's proof of theorem:asi (FOCS05-10page.tex:1606-1629)
has six steps; 1-5 are plank compositions (power,
selection, STPP2TPP, CU 4.1, wreath bound); step 6 closes
via `sum_le_of_multinomial_prod_pow_le`, whose hypothesis
is: for all N and compositions mu with sum(mu) = N,

```
multinomial(N, mu) * prod_i s_i^{mu_i} <= C^N
```

with `s_i = (|A_i||B_i||C_i|)^{omega/3}` and
`C = D_omega(G)`. Abbreviate `M = multinomial(N, mu)`,
`x = prod s_i^{mu_i}`, `y = D^N`. Steps 1-5 applied to
the multinomial-selected triples of type mu yield only

```
M! * x^M <= y^M        (*)
```

and the hypothesis needed is `M * x <= y`. (*) gives
`x <= y` by M-th roots but NOT `M * x <= y`:
counterexample M=2, x=1, y=sqrt(2). CKSU's "taking M-th
roots and letting N -> infinity" (tex:1621) hides a
nontrivial real-analysis argument. Sage-verified that
`M * x <= y` DOES hold for valid STPP triples — the
target inequality is true; the gap is purely in
extracting it from the capacity chain.

Resolution options: (1) dedicated extraction lemma using
the scaled family `ell * mu`; the iterated chain gives
`M(ell)! * x^{ell M(ell)} <= y^{ell M(ell)}`, close with
`le_of_pow_le_poly_mul_pow`. (2) direct combinatorial
proof of `M * x <= y` from STPP structure, bypassing the
chain. (3) entropy-based geom-arith step with no
multinomial prefactor. Recommended: option 1. The naive
lemma `M! * x^M <= y^M -> M * x <= y` is false (above);
it becomes true only using the full mu-family of
inequalities together, not one at a time.

The landed engine lemmas are `le_of_pow_le_poly_mul_pow`
(`GroupTPP/GeomArithInequality.lean:71`) and
`sum_le_of_multinomial_prod_pow_le` (:123). This target
stumped one prior prover dispatch (the Ca1 blocker). [A]

## binding spec: Tb1

Pl28 / Tb1 (critique-pl22 S): the STPP notion MUST be
`GroupTPP.STPPWreath.SimultaneousTPP` (STPPWreath.lean:168)
via a minimal additive-image bridge — no fresh STPP
definition, or Theorem B gets proved about the wrong
object. Primary kernel is K-TCSF (BCCGNSU Theorem A
verbatim) with the explicit constant
`epsilon = (1/2)*log((2/3)*2^(2/3))` ~ 0.02831; Theorem B
itself stays prose-only (no `exists epsilon_l` compactness form).
The `thm:main` reduction produces a BORDER tricolored
sum-free set; `lem:unborder` un-borders it. Slice rank is
not submultiplicative (arXiv:1705.09379); only
`sr(F tensor G) <= sr(F)*R(G)` and `sr(F tensor G) <= sr(F)*max dim` are
sound — reject any card stating the strong form. J(q) is
finite Chernoff analysis, not measure theory, repriced
800-1500 lines; realistic Track S total 4000-5500 lines.
Lucas is in Mathlib (`Mathlib.Data.Nat.Choose.Lucas`,
`lucas_theorem`); seam5's `Nat.lucas_prime_dvd` is a
phantom name, and seam5's claim that `SimultaneousTPP`
does not exist is false. Cite the paper by LaTeX label +
tex line from
`References/GroupTPP/arXiv-1605-06702/stpp-bound.tex`. [A]

## binding spec: Aw1 dead-end record

`abelian_wreath_family_tendsto_two` for general abelian H
with FIXED H and n->infinity is NOT provable via the CU
wreath cocycle construction alone. The cocycle u=(1,...,n)
requires n distinct elements in H, forcing |H| >= 2n,
which fails for fixed H as n grows; for H = Z/2Z the
construction degenerates (H_2 = H_1). Five alternative
routes were tried: (a) generalized cocycle — fails for
|H| < 2n; (b) reduction to cyclic via embedding —
pseudo-exponent transfer unclear; (c) direct computation
with {(pi,0)} subgroup — gives alpha->3, not 2; (d) STPP
capacity with fixed H — n is bounded by
|H|^{omega/(omega-1)}, cannot grow; (e) power-group H^k
trick — the theorem statement fixes H, not H^k. The
capacity route through `stpp_capacity_le` is the only
viable path. [A]

## binding spec: Clifford wave

The original Mathlib absence list was partly wrong —
Frobenius reciprocity (`indResHomEquiv`,
`indResAdjunction`) and orthogonality
(`FDRep.char_orthonormal`) EXIST; the two absences that
hold are the induced-rep dimension formula and Clifford
theory proper. Exhaustion is free via sum-of-squares;
per-rep irreducibility is owed. The general n!-carrier
lemma is already supplied by Df1
(`stpp_to_tpp_wreath_card [Group H]`, STPPWreath.lean:892).
Anchor every new def on H = C_2, n = 2, G = D_4. Hu8-1c
ruled general-H back in as a target; Cl5 must not
re-hedge. [A]

## binding spec: Ng1

The F3 answer-pinned suspect
`minNontrivIrrepDim_wreathS2_eq_two_of_ne_zero`
(WreathNg.lean:406-413, unused `not IsPerfect` hypothesis)
must be replaced by the unconditional theorem; 13 prose
"sorry" mentions rot in a sorry-free file; `Sager/`
pointers at :21/:83 are dead. The corollary target is
`bcgpu_cor_3_4_kernel` (BCGPUBarrier.lean:260-276);
there is no decl named `bcgpu_cor_3_4`. Lower bound
(tuple-of-partitions degree formula) is wreath Clifford
theory — unpriceable now; upper-bound-only. [A]

## stpp_capacity_le_of_wreath resolution options

`stpp_capacity_le` / `stpp_capacity_le_of_wreath`
(CKSU asi): still sorry in
`Proofs/GroupTPP/STPPWreath.lean` today. [M] The
blocker is extracting the multinomial prefactor from
the M-th root limit (CKSU tex:1606-1629). Three
recorded resolution options: (a) dedicated
`factorial_root_mul_le_of_factorial_pow_le`, (b) route
through `sum_le_of_multinomial_prod_pow_le`, (c) a
shorter CommGroup-only proof avoiding multinomial
selection. [A]

## same-name-different-statement hazards

- `abelian_wreath_family_tendsto_two` kept its NAME but
  changed statement (fixed-base -> growing-base family)
  after the original was found ungrounded — the (n!)^3
  witness violates pairwise bounds for fixed H at large
  n. Same-name-different-theorem across history. [M]
- `wreath_charDegree_bound` was weakened in place from
  `[Group H]` to `[CommGroup H]` (general case = shelved
  Gh1). [M]

## wreathGamma misstatement

The original `pseudoExponent_wreath_le_gamma` was unprovable:
`wreathGamma n` (two-term truncation
`2 + (1+log 2)/log n`) is strictly below
`gamma_exact(n) = log((2n)^n n!)/log(n!)` for all n >= 2,
because the dropped `O(1/(log n)^2)` remainder is
positive. n=2: exact 5 vs 4.443; n=3: exact 4 vs 3.541.
Repair option A (restate with exact gamma) was applied in
the committed file [M]. Status ladder: n=2..5
true via the trivial route, n >= 6 OPEN.

## rejected routes

- `matrixMonoidAlgEquiv` via `MonoidAlgebra.tensorEquiv`:
  doubly blocked by `CommSemiring`+`CommMonoid`
  constraints; rebuilt directly on `liftNCAlgHom`. [M]
- "CU Prop 11" phantom: the old theorem
  `abelian_wreath_family_tendsto_two` for FIXED abelian H
  cited "CU Prop 11"; no such proposition exists in any
  version of CU (math/0307321) or CKSU (math/0511460).
  CU's wreath theorem (Sec 7.4) uses the GROWING base
  `C_{2n}`; its cocycle witness needs 2n distinct base
  elements. The fixed-H claim's truth is UNKNOWN. [A]
