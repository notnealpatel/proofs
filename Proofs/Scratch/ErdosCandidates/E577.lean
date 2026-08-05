/-
  Erdős Problem #577 — vertex-disjoint 4-cycles (Erdős–Faudree).
  Status: proved (Wang 2010).  Tier D statement archive (the ~45-page
  case analysis is a campaign, not a lane).

  Verbatim statement (`goof erdos fetch 577`, pulled 2026-08-05):

    "If $G$ is a graph with $4k$ vertices and minimum degree at least
    $2k$ then $G$ contains $k$ vertex-disjoint $4$-cycles."

  DB remarks: conjecture of Erdős–Faudree; proved by Wang [Wa10]
  ("Proof of the Erdős-Faudree conjecture on quadrilaterals",
  Graphs Combin. 2010, 833–877).

  Mathlib inventory: `SimpleGraph.minDegree`, `SimpleGraph.cycleGraph`
  and copies (`⊑` via Copy.lean); vertex-disjoint packing has no
  Mathlib API — encoded below via a family of disjoint 4-sets each
  spanning a C₄ copy.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E577

open SimpleGraph

/-- `HasDisjointC4s G k`: `G` contains `k` vertex-disjoint 4-cycles —
    a family of pairwise-disjoint 4-element vertex sets, each carrying
    a 4-cycle of `G` (as a cyclic ordering with the four cycle edges
    present; chords allowed — a C₄ copy need not be induced). -/
def HasDisjointC4s {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) : Prop :=
  ∃ f : Fin k → (Fin 4 → V),
    (∀ i, Function.Injective (f i)) ∧
    (∀ i j, i ≠ j → ∀ a b, f i a ≠ f j b) ∧
    ∀ i, G.Adj (f i 0) (f i 1) ∧ G.Adj (f i 1) (f i 2) ∧
      G.Adj (f i 2) (f i 3) ∧ G.Adj (f i 3) (f i 0)

/-- Satisfiability: `K₄` contains one C₄ (`k = 1`).
    -- PROVABLE (decide). -/
example : HasDisjointC4s (⊤ : SimpleGraph (Fin 4)) 1 := by
  sorry

/-- **Erdős #577, Wang's theorem** ([Wa10]): a graph on `4k` vertices
    with minimum degree at least `2k` contains `k` vertex-disjoint
    4-cycles.

    Source text as in the header.  Guards: `1 ≤ k` (k = 0 is
    trivially true and the min-degree hypothesis at k = 0 is empty).

    Archive rationale: the statement is clean, but Wang's proof is a
    ~45-page extremal case analysis and Mathlib has no
    vertex-disjoint cycle packing layer — statement archive only per
    the candidates audit.  The k = 1 slice (4 vertices, min degree 2
    forces a C₄... false! C₄-free graphs on 4 vertices with min
    degree 2 — the triangle-plus-pendant has min degree 1; K₄ minus
    perfect matching = C₄ ✓; the diamond K₄⁻ contains C₄ ✓; the
    triangle with an isolated vertex has min degree 0.  On 4 vertices
    min degree 2 forces C₄ or the diamond… probe k = 1 by decide) is
    the entry sanity below. -/
theorem wang_erdos_faudree (k : ℕ) (hk : 1 ≤ k)
    (G : SimpleGraph (Fin (4 * k))) [DecidableRel G.Adj]
    (hdeg : 2 * k ≤ G.minDegree) :
    HasDisjointC4s G k := by
  sorry

/-- The `k = 1` instance — decide-scale: every graph on 4 vertices
    with min degree ≥ 2 contains a 4-cycle.
    -- PROVABLE (native_decide over the 2⁶ graphs on 4 vertices;
    or hand case analysis).  Entry sanity for the packing def. -/
theorem wang_k1 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (hdeg : 2 ≤ G.minDegree) :
    HasDisjointC4s G 1 := by
  sorry

/-- Sharpness sanity: min degree `2k − 1` does not suffice —
    K_{2k-1, 2k+1} has min degree 2k−1 and its C₄-packing is limited
    by the smaller side: at most ⌊(2k−1)/2⌋ = k−1 disjoint C₄s (each
    C₄ uses 2 vertices per side).  Recorded at k = 2: K_{3,5} on 8
    vertices, min degree 3, no 2 disjoint C₄s.
    -- PROVABLE (native_decide on an explicit 8-vertex bipartite
    encoding). -/
theorem sharpness_k2 :
    ∃ (G : SimpleGraph (Fin 8)) (_ : DecidableRel G.Adj),
      3 ≤ G.minDegree ∧ ¬ HasDisjointC4s G 2 := by
  sorry

end ErdosCandidates.E577

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 577` exactly.
   - Wang [Wa10] attribution and Erdos-Faudree conjecture provenance confirmed.
   - HasDisjointC4s encoding is faithful: Fin k -> Fin 4 -> V with per-cycle
     injectivity, pairwise vertex-disjointness, and the four cycle edges
     0-1, 1-2, 2-3, 3-0 correctly capture vertex-disjoint C4 copies
     (chords allowed, as intended).
   - Sharpness K_{3,5} arithmetic verified: 8 vertices, min degree 3 (5-side
     has degree 3), each C4 uses 2 per side, two disjoint C4s need 4 from the
     3-side -- impossible.  Claim is correct.
   - k=1 sanity rationale in docstring is sound.
-/
