/-
  Erdős Problem #80 — edges in many triangles (books).
  Status: open.  Tier C archive target.

  Verbatim statement (`goof erdos fetch 80`, pulled 2026-08-05):

    "Let $c>0$ and let $f_c(n)$ be the maximal $m$ such that every
    graph $G$ with $n$ vertices and at least $cn^2$ edges, where each
    edge is contained in at least one triangle, must contain a book of
    size $m$, that is, an edge shared by at least $m$ different
    triangles.

    Estimate $f_c(n)$. In particular, is it true that
    $f_c(n)>n^{\epsilon}$ for some $\epsilon>0$? Or
    $f_c(n)\gg \log n$?"

  DB remarks (Erdős–Rothschild): Alon–Trotter: f_c(n) ≪_c √n for
  c < 1/4.  Szemerédi (regularity): f_c(n) → ∞.  Edwards (unpub.) and
  Khadzhiivanov–Nikiforov [KhNi79] independently: f_c(n) ≥ n/6 for
  c > 1/4.  Fox–Loh [FoLo12]: f_c(n) ≤ n^{O(1/log log n)} for all
  c < 1/4 — disproving the n^ε conjecture.  Potechin [Po18] further
  partial improvements (comment).

  The c > 1/4 slice below uses the classical finite counting route,
  as presented in Bollobás–Nikiforov, Books in graphs (2005),
  Theorem 1, arXiv:math/0405080. The proof counts triangle/vertex
  equal-adjacency incidences and uses Cauchy's degree-square bound;
  it does not use a Kruskal–Katona or Turán supersaturation claim.

  Mathlib inventory: `SimpleGraph.cliqueFinset 3` for triangles;
  book size of an edge = number of common neighbours of its ends.
-/
import Combinatorics.Books.Edwards

set_option autoImplicit false

namespace ErdosCandidates.E80

open SimpleGraph Finset

variable {n : ℕ}

/-- `bookSize G u v`: the number of triangles sharing the edge
    `{u, v}` — i.e. common neighbours of `u` and `v`. -/
abbrev bookSize (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    ℕ :=
  ErdosCandidates.Books.bookSize G u v

/-- `EveryEdgeInTriangle G`: each edge lies in at least one triangle. -/
abbrev EveryEdgeInTriangle (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Prop :=
  ErdosCandidates.Books.EveryEdgeInTriangle G

/-- In `K₄`, the edge joining vertices `0` and `1` has two common neighbours. -/
theorem k4_bookSize_zero_one : bookSize (⊤ : SimpleGraph (Fin 4)) 0 1 = 2 := by
  decide

/-- Ground truth: in `K₄` every edge is in exactly 2 triangles.
    -- PROVABLE (decide). -/
example : bookSize (⊤ : SimpleGraph (Fin 4)) 0 1 = 2 := by
  exact k4_bookSize_zero_one

/-- **Edwards / Khadzhiivanov–Nikiforov** (the c > 1/4 slice):
    more than `n²/4` edges force a book of size at least `n/6`.
    The unchanged archive conclusion `n ≤ 6·bookSize + 5` is a
    division-free weakening of the classical bound, not a replacement
    for its constant. The `EveryEdgeInTriangle` premise is retained.

    The production proof follows the equal-adjacency incidence count
    and degree-square inequality in Bollobás–Nikiforov, *Books in
    graphs*, European J. Combin. 26 (2005), 259–270, Theorem 1
    (arXiv:math/0405080); ordered counts avoid induced four-vertex
    infrastructure. Edwards' unpublished result and the independent
    Khadzhiivanov–Nikiforov (1979) result are classical, not new here. -/
theorem edwards_kn_book (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 6 ≤ n)
    (he : n ^ 2 < 4 * G.edgeFinset.card)
    (ht : EveryEdgeInTriangle G) :
    ∃ u v : Fin n, G.Adj u v ∧ n ≤ 6 * bookSize G u v + 5 := by
  exact ErdosCandidates.Books.edwards_kn_book G hn he ht

/-- **Erdős #80, first conjecture — REFUTED by Fox–Loh** ([FoLo12]):
    it is NOT true that for `c < 1/4` one has `f_c(n) > n^ε`; there
    are graphs with `cn²` edges, every edge in a triangle, and max
    book size `≤ n^{C/log log n}`.  Archived as the negated form:
    for every `ε > 0` and `c < 1/4`, witnesses exist infinitely often.
    (Fox–Loh's construction is a pentagon-blowup with modifications —
    explicit but analytically sized.) -/
theorem fox_loh_refutation (c ε : ℝ) (hc : 0 < c) (hc4 : c < 1 / 4)
    (hε : 0 < ε) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        c * n ^ 2 ≤ (G.edgeFinset.card : ℝ) ∧
        EveryEdgeInTriangle G ∧
        ∀ u v : Fin n, G.Adj u v → (bookSize G u v : ℝ) < (n : ℝ) ^ ε := by
  sorry

/-- **Szemerédi's regularity consequence**, archived: for every fixed
    `c > 0`, `f_c(n) → ∞` — every bound `m` is eventually forced.
    The only known lower bounds at c < 1/4; regularity is in Mathlib
    (`SzemerediRegularity`), making this a heavy-but-conceivable
    target. -/
theorem szemeredi_book_unbounded (c : ℝ) (hc : 0 < c) (m : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        c * n ^ 2 ≤ (G.edgeFinset.card : ℝ) →
        EveryEdgeInTriangle G →
        ∃ u v : Fin n, G.Adj u v ∧ m ≤ bookSize G u v := by
  sorry

/-- `K₄` satisfies the density and triangle hypotheses jointly. -/
theorem k4_dense_everyEdgeInTriangle :
    (4 : ℕ) ^ 2 < 4 * (⊤ : SimpleGraph (Fin 4)).edgeFinset.card ∧
      EveryEdgeInTriangle (⊤ : SimpleGraph (Fin 4)) := by
  unfold EveryEdgeInTriangle
  decide

/-- Sanity: the hypothesis pair is jointly satisfiable at a nontrivial
    model — `K₄` has 6 > 4²/4 = 4 edges, every edge in a triangle.
    -- PROVABLE (decide). -/
example : (4 : ℕ) ^ 2 < 4 * (⊤ : SimpleGraph (Fin 4)).edgeFinset.card ∧
    EveryEdgeInTriangle (⊤ : SimpleGraph (Fin 4)) := by
  exact k4_dense_everyEdgeInTriangle

end ErdosCandidates.E80

/- Formalization scope: only the classical dense-graph slice is discharged.
   The definitions above are transparent aliases of the production counts.
   The adopted K₄ checks are unchanged. Fox–Loh and Szemerédi remain
   OPEN formalization obligations, with their original sorry contracts.
   The weaker +5 conclusion is intentional; it is not the exact classical
   constant and this file makes no historical source-review PASS claim.
-/

