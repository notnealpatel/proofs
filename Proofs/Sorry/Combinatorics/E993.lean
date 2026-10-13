/-
  Erdős Problem #993 — unimodality of the independent-set sequence of
  trees and forests.
  Historical archive metadata described the tree case as open and attributed
  the general-graph negative result to AMSE 1987. These status and attribution
  claims have not been freshly checked against primary sources in this episode.

  Archived DB wording (the inherited record cites `goof erdos fetch 993`
  and 2026-08-05; not verified here as a verbatim primary-source quotation):

    "The independent set sequence of any tree or forest is unimodal.

    In other words, if $i_k(G)$ counts the number of independent sets of
    vertices of size $k$ in a graph $G$, and $T$ is any tree or forest,
    then for some $m\geq 0$
    $$i_{0}(T)\leq i_{1}(T)\leq\cdots\leq i_{m}(T)\geq i_{m+1}(T)\geq
    i_{m+2}(T)\geq\cdots.$$"

  Historical DB remarks attributed the question to Alavi–Malde–Schwenk–Erdős
  [AMSE87] and reported that general graphs realize every inequality pattern.
  The inherited comment summary reported exhaustive checks through 29 vertices
  (JakeMallen, BrettRey; 5.4·10⁹ trees at n = 29), PatternBoost sampling to 101
  vertices, log-concavity failures from 26 vertices (Kadrawi–Levit 2023), and
  a Hoggar-based forest reduction (Will Blair's comment). These are historical
  reports, not primary-source or computational verification performed here;
  no current tree-conjecture status or exhaustive-check claim is certified.

  The formalization counts independent sets via `SimpleGraph.cliqueFinset`
  on the complement and uses `SimpleGraph.IsTree` from Acyclic.lean.
  Its `Unimodal` predicate is defined in the production module. An inherited
  unsuccessful leandoc search does not establish absence of a Mathlib notion.
  The constructive P₄ check, canonical convolution, and explicit general-graph
  counterexample are independent of the historical attribution. The latter is
  not identified with the original AMSE witness.
-/
import Combinatorics.IndependencePolynomial
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

namespace ErdosCandidates.E993

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ground truth: the path P₄ (4 vertices, 3 edges) has independent-set
    sequence 1, 4, 3, 0, 0, … — unimodal with peak m = 1.  (Corrected
    per review: no 3 vertices of P₄ are pairwise non-adjacent, so
    i₃ = 0.) Checked by ordinary kernel `decide`. -/
example :
    indepCount (pathGraph 4) 0 = 1 ∧ indepCount (pathGraph 4) 1 = 4 ∧
    indepCount (pathGraph 4) 2 = 3 ∧ indepCount (pathGraph 4) 3 = 0 := by
  decide

/-- **Erdős #993, archived tree conjecture (unproved here)**: the
    independent-set sequence of any finite tree is unimodal.

    This remains an admission: the finite production episode does not
    resolve the tree conjecture. -/
theorem tree_unimodal (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.IsTree) :
    Unimodal (indepCount G) := by
  sorry

/-- The disjoint-union convolution, with the existential witness fixed to
    the canonical graph sum. This is the polynomial-product slice of the
    forest reduction, not a proof of the archived unimodality conjecture. -/
theorem indepCount_disjoint_union {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) :
    ∃ (U : SimpleGraph (V ⊕ W)) (_ : DecidableRel U.Adj),
      indepCount U k =
        ∑ p ∈ Finset.antidiagonal k, indepCount G p.1 * indepCount H p.2 := by
  exact ⟨G ⊕g H, inferInstance, indepCount_sum G H k⟩

/-- General graphs need not have unimodal independent-set sequences.
    The explicit witness here is the join of K₁₀ with an edgeless six-vertex
    graph. Its counts at sizes 1, 2, 3 are 16, 15, 20. This is not a claim
    of minimality or identification with the original AMSE witness.
    The former K₄-plus-isolated-vertices anecdote was arithmetically wrong:
    a disjoint union is not this join construction. -/
theorem amse_general_graphs_fail :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      ¬ Unimodal (indepCount G) := by
  exact ⟨16, valleyGraph, inferInstance, valleyGraph_not_unimodal⟩

/-- Unimplemented small-tree sweep target (at most ten vertices).
    No graph enumeration or sweep is performed in this episode. -/
theorem tree_sweep_small (n : ℕ) (hn : n ≤ 10) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hT : G.IsTree) :
    Unimodal (indepCount G) := by
  sorry

end ErdosCandidates.E993

/- HISTORICAL REVIEW NOTE
   The inherited review was labelled "flash, 2026-08-05". Its assertions of
   verbatim source fidelity, attribution correctness, and an eventual PASS
   are not retained as source certification: primary sources were not freshly
   verified in this episode.

   The arithmetic issue recorded there was i₃(P₄) = 1 rather than 0. The current
   example kernel-checks the corrected counts 1, 4, 3, 0. `Unimodal` retains
   its existential peak and inequalities over all natural-number indices;
   `indepCount` retains cardinality of complement cliques. These formal results
   do not certify the historical DB quotation, computational comment reports,
   current conjecture status, or identification of an original AMSE witness.
-/

