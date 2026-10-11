/-!
# Group barriers, Lie targets, chart-USP, and sieve: documentation archive

## Current archive status and scope

This is a documentation-only module in `Sorry/`, not a formal statement,
proof, admission, or complete formalization. The historical source claims
below remain sourced claims: accepting this comment with Lean proves none
of them. No continuous group, Lie pseudo-exponent, action, asymptotic family,
or enumeration certificate is invented. This migration adds no imports or
formal declarations and does not change existing finite results.

## Remaining obligations and hypotheses by source

* arXiv:1605.06702: assemble the explicit bounded-exponent abelian STPP
  barrier. Preserve the quantifier order over each exponent bound `l`, the
  associated `ε_l`, all family hypotheses and slice-rank/cap-set asymptotics.
* arXiv:1605.09223: provide the progression-free family over `(ℤ/3ℤ)^n`
  and the actual little-o quantification for `|A| = o(2.756^n)` as recorded
  in the card, including the source's meaning of its numerical base.
  Finite bounds are not the uniform asymptotic statement.
* arXiv:1712.02302: retain the named BCCGU bounded-exponent,
  bounded-length nilpotent, and slice-rank/STPP barriers with their separate
  family restrictions. These are not interchangeable with BCGPU inequalities.
* arXiv:2204.03826: define the continuous Lie-group pseudo-exponent framework
  faithfully. The transfer to the matrix-multiplication exponent is an open
  source question, not an available theorem to assert or silently assume.
* arXiv:math/0307321: supply the real `SL_n` subgroup construction using upper
  and lower unitriangular and orthogonal subgroups, its TPP proof, dimension
  hypotheses, and continuous pseudo-exponent estimate.
* arXiv:math/0511460: construct quantitative chart/USP families, establish USP
  capacity and all parameter inequalities, and justify the `ω < 2.41`
  derivation. A useful asymptotic family needs nonempty carriers and
  quantitative growth, not empty or width-zero finite packaging.
* gcc-2012-0006: reproduce the entire finite group-sieve table. Missing data
  include its precise group universe, representation data, normalization,
  pruning rules, completeness certificate, and all capacity/barrier outputs.

The card does not give full theorem formulas for these targets. Their exact
constants, permitted parameter ranges, field/manifold conventions, and source
revision choices remain source-extraction obligations; this archive neither
supplies them nor weakens the conclusions to existing finite kernels.

## Existing pieces and explicit boundaries

`Proofs/GroupTPP/ChartUSP.lean` implements a finite conditional bridge using
local right-quotient TPP, an injective selected word family, and coordinate
separation with cyclic threading `(u,v)`, `(v,w)`, `(w,u)`. Its theorem uses
`[CommGroup H] [Fintype H] [DecidableEq H]`; the product-carrier cardinality
lemma and width-one two-word certificate over `Multiplicative (ZMod 3)`
make the finite scope concrete. The header expressly supplies no chart
construction, word-family lower bound, or asymptotic estimate. Empty
selections and width zero are allowed in the general finite implication;
that does not witness an asymptotically useful family.

`Proofs/GroupTPP/BCGPUBarrier.lean` describes finite representation-theoretic
and normalizer/center inequalities and a per-group Lie-type kernel, not the
continuous Lie claims or the BCCGU asymptotic family barriers. Existing
slice-rank/cap-set infrastructure is not an assembly of the named asymptotics.
`Proofs/Sorry/GroupTPP/STPPWreath.lean` separately archives the central
admitted capacity and wreath skeleton; it explicitly retains `sorryAx`
dependence. The finite ChartUSP bridge does not pay that admission or derive
`ω < 2.41`. Individual group computations do not certify an exhaustive sieve.
These source/header boundaries were inspected, not independently proof-audited
or rebuilt here.

## Historical/source-card subsection — complete current card verbatim

# Group-theoretic barriers, continuous Lie targets, and chart-USP residuals

This card retains source-level obligations that are not the central STPP capacity skeleton.

- **arXiv:1605.06702 — bounded-exponent abelian STPP barrier.** Formalize the explicit `ε_l` barrier with its slice-rank/cap-set asymptotic and quantifier order for every exponent bound `l`. Existing slice-rank and cap-set results do not yet assemble this theorem.
- **arXiv:1605.09223 — Ellenberg–Gijswijt cap-set little-`o`.** Formalize that every progression-free `A ⊆ (ℤ/3ℤ)^n` satisfies `|A| = o(2.756^n)` with the source's quantifier order and asymptotic meaning. Finite EG machinery or checked instances does not establish this little-`o` theorem.
- **arXiv:1712.02302 — named BCCGU barriers.** Formalize the stated bounded-exponent, bounded-length nilpotent, and slice-rank/STPP barrier corollaries with their family hypotheses. The BCGPU barrier file proves different finite representation-theoretic inequalities and is not a substitute.
- **arXiv:2204.03826 — continuous Lie claims.** Formalize the Lie-group pseudo-exponent framework and the open transfer question relating Lie exponents to the matrix-multiplication exponent. Finite-group kernels and BCGPU bounds do not establish the continuous claims.
- **arXiv:math/0307321 — continuous Lie pseudo-exponent.** Formalize the `SL_n(R)` upper/lower-unitriangular and orthogonal subgroup TPP construction and its pseudo-exponent bound. The finite Cohn–Umans capacity API is not this continuous target.
- **arXiv:math/0511460 — chart-USP route.** `Proofs/GroupTPP/ChartUSP.lean` now proves the finite coordinate-separation-to-STPP implication, product-carrier cardinalities, and a nonempty two-word example over `Multiplicative (ZMod 3)`. This is a finite packaging of CKSU's local chart construction, not a new asymptotic family. Remaining work is the quantitative chart/USP family construction, USP capacity and parameter inequalities, and the claimed `ω < 2.41` derivation. The separate central STPP/wreath capacity admission lives in `Proofs/Sorry/GroupTPP/STPPWreath.lean`; its old Formalize card has been retired as an implemented admission, not as proved mathematics.
- **gcc-2012-0006 — exhaustive group-sieve table.** Reproduce and validate the complete finite group-sieve table, including the enumerated groups, representation data, pruning rules, and all reported capacity/barrier outputs. Existing individual group lemmas are not an exhaustive certificate.

**Status:** partial finite implementation; source-level asymptotic, continuous, and exhaustive-certificate obligations remain. The finite chart bridge above is complete; it does not settle those remaining obligations. No blanket claim that all chart construction is unimplemented is intended.

-/
