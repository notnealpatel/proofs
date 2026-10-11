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

  Audit note (candidates doc): the c > 1/4 slice leans on a
  Turán-type input; Mathlib NOW has Turán machinery
  (`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`,
  Extremal/Turan.lean — leandoc hit), so the Edwards bound is more
  approachable than the doc assumed.  Archive + attempt the c > 1/4
  slice.

  Mathlib inventory: `SimpleGraph.cliqueFinset 3` for triangles;
  book size of an edge = number of common neighbours of its ends.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E80

open SimpleGraph Finset

variable {n : ℕ}

/-- `bookSize G u v`: the number of triangles sharing the edge
    `{u, v}` — i.e. common neighbours of `u` and `v`. -/
def bookSize (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    ℕ :=
  (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card

/-- `EveryEdgeInTriangle G`: each edge lies in at least one triangle. -/
def EveryEdgeInTriangle (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Prop :=
  ∀ u v : Fin n, G.Adj u v → 1 ≤ bookSize G u v

/-- Ground truth: in `K₄` every edge is in exactly 2 triangles.
    -- PROVABLE (decide). -/
example : bookSize (⊤ : SimpleGraph (Fin 4)) 0 1 = 2 := by
  sorry

/-- **Edwards / Khadzhiivanov–Nikiforov** (the c > 1/4 slice — the
    clean target): if `G` has more than `n²/4` edges and every edge is
    in a triangle, then some edge lies in at least `n/6` triangles.
    Stated division-free: `n² < 4·#edges` and conclusion
    `n ≤ 6·bookSize + 5` (i.e. bookSize ≥ ⌈(n−5)/6⌉ ≥ n/6 − 1; pin
    the exact constant to the KhNi79 paper during the campaign —
    the DB's "≥ n/6" hides floor conventions).

    Attack: supersaturation over Turán — a graph over the Turán
    threshold has an edge in many triangles by
    Kruskal–Katona/counting; Mathlib's new Extremal/Turan.lean
    supplies the extremal structure.  Effort M–L. -/
theorem edwards_kn_book (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 6 ≤ n)
    (he : n ^ 2 < 4 * G.edgeFinset.card)
    (ht : EveryEdgeInTriangle G) :
    ∃ u v : Fin n, G.Adj u v ∧ n ≤ 6 * bookSize G u v + 5 := by
  sorry

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

/-- Sanity: the hypothesis pair is jointly satisfiable at a nontrivial
    model — `K₄` has 6 > 4²/4 = 4 edges, every edge in a triangle.
    -- PROVABLE (decide). -/
example : (4 : ℕ) ^ 2 < 4 * (⊤ : SimpleGraph (Fin 4)).edgeFinset.card ∧
    EveryEdgeInTriangle (⊤ : SimpleGraph (Fin 4)) := by
  sorry

end ErdosCandidates.E80

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 80` exactly.
   - Attributions correct: Erdős–Rothschild; Alon–Trotter; Szemerédi
     regularity; Edwards unpub. + Khadzhiivanov–Nikiforov [KhNi79] 1979;
     Fox–Loh [FoLo12] 2012; Potechin [Po18] (comment).
   - `bookSize` correctly counts common neighbors (triangles sharing an edge).
   - K_4 sanity: bookSize = 2 correct; 16 < 24 correct.
   - Division-free encoding `n^2 < 4 * edges` faithfully captures c > 1/4;
     conclusion `n <= 6 * bookSize + 5` is a floor-safe weakening of >= n/6,
     acknowledged in the docstring.
   - Fox-Loh refutation correctly negates the epsilon-power conjecture for
     c < 1/4: witnesses exist infinitely often with bookSize < n^epsilon.
   - Szemerédi unboundedness statement correctly universally quantifies
     over m with eventual N.
-/
