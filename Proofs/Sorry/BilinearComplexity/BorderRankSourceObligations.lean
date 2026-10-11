/-!
# Matrix-multiplication border-rank source obligations: documentation archive

## Current archive status and scope

This is a documentation-only module in `Sorry/`, not a formal statement,
proof, admission, or complete formalization. It introduces no border-rank
object, tensor, action, or hypothesis. The published source result remains
unpaid here. Compiling this comment checks Lean's acceptance of the archive,
not the truth of the source claim or a border-rank theorem.

The dispatch named `Formalize/MatrixMultiplication-BorderRank.md`; the full
current card at this assigned base is instead
`Formalize/MatrixMultiplication-BorderRank-bound.md`, preserved below.

## Remaining obligation, hypotheses, and source conventions

Source: Landsberg–Ottaviani, arXiv:1112.6007. The consumer still needs the
exact rectangular matrix-multiplication theorem and corollary, not merely a
rank-locus vanishing implication. Recover the source's dimension ranges,
field/base-space assumptions, flattening choice, submatrix indices, and
numerical lower bound from the source before stating it. The card does not
supply those formulas or theorem numbers; this archive does not guess them.
The unpaid bridge identifies the actual rectangular matrix-multiplication
tensor with that chosen flattening and proves the dimension-indexed rank or
determinant estimate, including all injectivity and size hypotheses.

## Existing pieces and their boundaries

The header of `Proofs/AlgComplexity/Vp2/BorderRank.lean` describes a cubic
coordinate model `Fin n → Fin n → Fin n → k`, honest rank decompositions,
polynomial-closure `BorderRankLE`, flattening-rank bounds, submatrix-minor
vanishing, and generic-minor evaluation/nonvanishing. These are ingredients,
not an identification with the source's rectangular tensor or specialized
flattening. Its explicit honesty note leaves the bridge over the complex
numbers from polynomial closure to classical border rank (Segre secant,
Zariski and Euclidean closures) unpaid. That convention must not silently
be replaced by the classical conclusion. No production pieces were rebuilt
or independently audited by this documentation migration.

## Historical/source-card subsection — complete current card verbatim

# Exact matrix-multiplication border-rank residual

- **Source:** arXiv:1112.6007, Landsberg–Ottaviani.
- **Mathematical status:** published exact border-rank lower bound for rectangular matrix multiplication, not fully formalized.
- **Work status:** hard-blocked.
- **Remaining target:** formalize the exact theorem and corollary, with their rectangular dimensions, flattening/submatrix hypotheses, and border-rank conclusion. The generic flattening vanishing API in `Proofs/AlgComplexity/Vp2/BorderRank.lean` is only an ingredient.
- **Next obligation:** connect the matrix-multiplication tensor to the source's chosen flattening and prove the dimension-indexed determinant/rank estimate without weakening the statement to a generic necessary condition.

-/
