/-
  Erdős Problem #130 — integer-distance graphs and the Anning–Erdős
  theorem.
  Status: open (main chromatic question); the Anning–Erdős theorem,
  integer-axis example, and no-infinite-clique corollary are proved in
  the independent production module.

  Verbatim statement (`goof erdos fetch 130`, pulled 2026-08-05):

    "Let $A\subset\mathbb{R}^2$ be an infinite set which contains no
    three points on a line and no four points on a circle. Consider
    the graph with vertices the points in $A$, where two vertices are
    joined by an edge if and only if they are an integer distance
    apart.

    How large can the chromatic number and clique number of this graph
    be? In particular, can the chromatic number be infinite?"

  DB remarks: asked by Andrásfai–Erdős.  Erdős [Er97b] also asked
  whether such a graph could contain an infinite complete graph —
  impossible by Anning–Erdős [AnEr45]: an infinite set in ℝ² with ALL
  pairwise distances integral must be collinear.

  Mathlib inventory (leandoc 2026-08-05): `EuclideanSpace ℝ (Fin 2)`,
  `dist`, `Collinear ℝ`, `Set.Infinite`; concyclic:
  `EuclideanGeometry.Cospherical` exists (Mathlib geometry) for the
  no-four-on-a-circle condition. The original paper, N. H. Anning and
  P. Erdős, “Integral distances”, Bull. AMS 51 (1945), 598–600,
  DOI 10.1090/S0002-9904-1945-08407-9, uses an angular proof.
  Erdős's second December 1945 note (DOI 10.1090/S0002-9904-1945-08490-0)
  gives a hyperbola proof, reproduced in arXiv:2401.10821 §1.3.
  The production proof below is an independent coordinate-quadratic
  argument, not a formalization of either historical proof.
-/
import Combinatorics.IntegralDistances.AnningErdos

set_option autoImplicit false

namespace ErdosCandidates.E130

open EuclideanGeometry

/-- Points of the plane. -/
abbrev Plane : Type := AnningErdos.Plane

/-- `IntegralDistances A`: all pairwise distances in `A` are integers
    (witnessed in ℤ via a cast, so no `Nat.floor` junk). -/
abbrev IntegralDistances (A : Set Plane) : Prop :=
  AnningErdos.IntegralDistances A

/-- Satisfiability: any subset of the integer points on the x-axis has integral
    distances — e.g. `{(0,0), (1,0), (2,0)}`; indeed ℤ×{0} is an
    infinite example, which is why collinearity is the conclusion and
    not a contradiction. The `WithLp.toLp` wrapper constructs the
    Euclidean-space point with precisely these coordinates. -/
example : IntegralDistances (Set.range (fun n : ℤ =>
    (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (n : ℝ) else 0) : Plane))) :=
  AnningErdos.integer_axis_integral

/-- **Anning–Erdős theorem (1945) — the proof target**: an infinite
    set in ℝ² with all pairwise distances integral is collinear.

    Source (DB remarks): "an infinite set in ℝ² with all pairwise
    distances integral must be collinear" [AnEr45].

    Independent proof: choose three noncollinear points o, a, b.
    The signed differences dist(p,a)-dist(p,o) and dist(p,b)-dist(p,o)
    are integers in bounded intervals, so have finitely many patterns.
    For a fixed pattern, squaring actual distance equalities gives two
    linear equations. Their nonzero coordinate determinant expresses
    p-o as an affine function of r = dist(p,o). The norm equation is a
    quadratic in r. If its coefficients all vanish, the constant vector
    vanishes and both focus vectors become multiples of a single vector,
    contradicting the determinant. Thus each pattern has finitely many
    radii, each determining at most one point. Infinitude is impossible.
    No general conic-intersection or hyperbola-pair claim is assumed. -/
theorem anning_erdos (A : Set Plane) (hA : A.Infinite)
    (hd : IntegralDistances A) :
    Collinear ℝ A :=
  AnningErdos.anning_erdos A hA hd

/-- The integer-distance graph on a point set: edges join points at
    integer distance (distinct points). -/
abbrev intDistGraph (A : Set Plane) : SimpleGraph A :=
  AnningErdos.intDistGraph A

/-- **Erdős #130, main question (OPEN)**: can the chromatic number of
    the integer-distance graph on an infinite `A` (no 3 collinear, no
    4 concyclic) be infinite?  Stated as the existence question:
    is there such an `A` whose graph admits no proper finite coloring.
    `Cospherical` is Mathlib's concyclicity (in the plane: on a common
    circle). -/
theorem erdos_130_chromatic :
    ∃ A : Set Plane, A.Infinite ∧
      (∀ s ⊆ A, s.ncard = 3 → ¬ Collinear ℝ s) ∧
      (∀ s ⊆ A, s.ncard = 4 → ¬ Cospherical s) ∧
      ∀ k : ℕ, ¬ (intDistGraph A).Colorable k := by
  sorry

/-- **Clique-number corollary of Anning–Erdős** — the formalizable
    slice adjacent to the main theorem: under the same hypotheses
    (no 3 collinear), the integer-distance graph has no infinite
    clique.  Follows from `anning_erdos` applied to the clique (an
    infinite clique is an infinite set with pairwise integral
    distances, hence collinear — contradicting no-3-collinear).
    No no-four-concyclic hypothesis is needed. -/
theorem no_infinite_clique (A : Set Plane)
    (h3 : ∀ s ⊆ A, s.ncard = 3 → ¬ Collinear ℝ s)
    (B : Set A) (hB : B.Infinite)
    (hclique : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → (intDistGraph A).Adj x y) :
    False :=
  AnningErdos.no_infinite_clique A h3 B hB hclique

end ErdosCandidates.E130

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS for archived statement fidelity, not a proof review.
   This historical review does not certify the later independent
   coordinate-quadratic proof in the production module.
   - Verbatim statement matches `goof erdos fetch 130` exactly.
   - Attribution Andrásfai–Erdős correct; Anning–Erdős [AnEr45] 1945 correct.
   - `Cospherical` is the right Mathlib notion: its docstring explicitly
     states "In two dimensions, this is the same thing as being concyclic."
   - `Collinear ℝ` and `EuclideanSpace ℝ (Fin 2)` are appropriate types.
   - `intDistGraph` correctly encodes integer-distance adjacency via ℤ-cast.
   - `no_infinite_clique` correctly derives from Anning–Erdős as described
     in the DB remarks.
-/
