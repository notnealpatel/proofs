/-
  Erdős Problem #130 — integer-distance graphs and the Anning–Erdős
  theorem.
  Status: open (main question); the Anning–Erdős theorem (1945) is the
  proof target.  Tier C (opens a Euclidean plane-geometry lane).

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
  no-four-on-a-circle condition.  The Anning–Erdős argument is a
  classical self-contained hyperbola-counting proof — the right entry
  point for a plane-geometry lane the repo has not opened.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E130

open EuclideanGeometry

/-- Points of the plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- `IntegralDistances A`: all pairwise distances in `A` are integers
    (witnessed in ℤ via a cast, so no `Nat.floor` junk). -/
def IntegralDistances (A : Set Plane) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∃ z : ℤ, dist x y = (z : ℝ)

/-- Satisfiability: any set of collinear integer points has integral
    distances — e.g. `{(0,0), (1,0), (2,0)}`; indeed ℤ×{0} is an
    infinite example, which is why collinearity is the conclusion and
    not a contradiction.  -- PROVABLE (norm computation). -/
example : IntegralDistances (Set.range (fun n : ℤ =>
    (fun i : Fin 2 => if i = 0 then (n : ℝ) else 0 : Plane))) := by
  sorry

/-- **Anning–Erdős theorem (1945) — the proof target**: an infinite
    set in ℝ² with all pairwise distances integral is collinear.

    Source (DB remarks): "an infinite set in ℝ² with all pairwise
    distances integral must be collinear" [AnEr45].

    Proof sketch (attack plan): suppose x, y, z ∈ A not collinear.
    For any further point p, |d(p,x) − d(p,y)| is an integer at most
    d(x,y), so p lies on one of finitely many hyperbolae with foci
    x, y; similarly for the pair (x, z).  Two distinct conic families
    intersect in ≤ 4 points each; finitely many hyperbola pairs give
    finitely many candidate points — contradicting infinitude.
    Formalization load: hyperbola = level set of |dist − dist|;
    the finite-intersection input is the real work (algebraic —
    two distinct conics meet in ≤ 4 points; Bezout-flavored;
    Mathlib's `Polynomial` in two variables via `MvPolynomial` or a
    hand-rolled resultant for the special conic case).
    Effort M–L per candidates audit. -/
theorem anning_erdos (A : Set Plane) (hA : A.Infinite)
    (hd : IntegralDistances A) :
    Collinear ℝ A := by
  sorry

/-- The integer-distance graph on a point set: edges join points at
    integer distance (distinct points). -/
def intDistGraph (A : Set Plane) : SimpleGraph A where
  Adj x y := x ≠ y ∧ ∃ z : ℤ, dist x.1 y.1 = (z : ℝ)
  symm := by
    intro x y h
    exact ⟨h.1.symm, by obtain ⟨z, hz⟩ := h.2; exact ⟨z, by rwa [dist_comm]⟩⟩
  loopless := by intro x h; exact h.1 rfl

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
    -- PROVABLE from `anning_erdos` (effort S). -/
theorem no_infinite_clique (A : Set Plane)
    (h3 : ∀ s ⊆ A, s.ncard = 3 → ¬ Collinear ℝ s)
    (B : Set A) (hB : B.Infinite)
    (hclique : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → (intDistGraph A).Adj x y) :
    False := by
  sorry

end ErdosCandidates.E130

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 130` exactly.
   - Attribution Andrásfai–Erdős correct; Anning–Erdős [AnEr45] 1945 correct.
   - `Cospherical` is the right Mathlib notion: its docstring explicitly
     states "In two dimensions, this is the same thing as being concyclic."
   - `Collinear ℝ` and `EuclideanSpace ℝ (Fin 2)` are appropriate types.
   - `intDistGraph` correctly encodes integer-distance adjacency via ℤ-cast.
   - `no_infinite_clique` correctly derives from Anning–Erdős as described
     in the DB remarks.
-/
