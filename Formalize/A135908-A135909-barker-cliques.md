seq:     A135908, A135909
claim:   barker-commuting-clique-recurrences
status:  open
stmt:    S
proof:   L
module:  Proofs/Xlib/CommProbBound.lean,
         HigherCommProb.lean (commuting structure)
source:  OEIS A135908 and A135909 formulas, Colin
         Barker, 2013-07-26

CLAIM
  a(n) = clique number of the commuting graph of S_n
  (A135908) resp. A_n (A135909): vertices = group
  elements, edges = commuting pairs; clique number =
  largest set of pairwise-commuting elements = largest
  abelian subgroup order (a pairwise-commuting set
  generates an abelian subgroup). Conjectures:
    S_n: a(n) = a(n-1) + 3a(n-3) - 3a(n-4)  (n > 7)
    A_n: same recurrence                     (n > 6)
  with explicit rational generating functions
  in-entry.

LEAN
  SimpleGraph.cliqueNum exists; commuting graph is a
  one-line SimpleGraph def (novel in Lean). Statement
  S.

ROUTE
  Reduces to: maximal abelian subgroups of S_n are
  (up to the boundary cases) direct products of
  3-cycle groups on disjoint supports, giving
  b(n) = max(b(n-1), 3*b(n-3)) and hence the linear
  recurrence and g.f. The underlying max-abelian-
  subgroup theorem (Bercov-Moser flavor) is real
  mathematics — L — but crisp, self-contained, and
  novel in Lean; the recurrence then falls out
  mechanically. Do small n by decide-style
  computation to anchor.

EVIDENCE
  Recurrence fits all computed terms in-entry.
