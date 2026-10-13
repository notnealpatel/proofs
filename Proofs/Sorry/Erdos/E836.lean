/-
  Erdős Problem #836 — intersecting 3-chromatic r-uniform hypergraphs.
  Status: open (second question possibly closed — see warning below).
  Tier UA attack target.

  Verbatim statement (`goof erdos fetch 836`, pulled 2026-08-05):

    "Let $r\geq 2$ and $G$ be a $r$-uniform hypergraph with chromatic
    number $3$ (that is, there is a $3$-colouring of the vertices of $G$
    such that no edge is monochromatic).

    Suppose any two edges of $G$ have a non-empty intersection. Must $G$
    contain $O(r^2)$ many vertices? Must there be two edges which meet
    in $\gg r$ many vertices?"

  ⚠ FIDELITY NOTE: the DB's parenthetical defines "chromatic number 3"
  as *3-colorability with no monochromatic edge* — NOT the standard
  "χ = 3 exactly".  In the Erdős–Lovász context [ErLo75] the intended
  meaning is "not 2-colorable" (χ ≥ 3, no Property B); an intersecting
  hypergraph with χ ≤ 2... any hypergraph is 3-colorable if it has few
  vertices, so the parenthetical alone would be nearly vacuous.  We
  formalize BOTH conjuncts: 3-colorable AND not 2-colorable (χ = 3 in
  the standard sense for edges of size ≥ 2).  The reviewer should
  scrutinize this choice against [ErLo75].

  DB remarks: Alon refuted the first question (an intersecting
  3-chromatic r-graph with ≍ 4^r/√r vertices; explicit construction on
  X ∪ Y, |X| = 2r−2, Y = balanced partitions of X).  Erdős–Lovász
  [ErLo75]: two edges must share ≫ r/log r vertices.  Fano plane: edges
  need not meet in r−1 points.  Comment (Apr 2026): GPT-5.5 Pro claims
  a proof of the second question (≫ r); posted, not yet reviewed —
  re-fetch the live entry before treating it as closed.

  Repo adjacency: `Proofs/Erdos/ErdosLovasz.lean` (the g(k)
  covering-number work from the same paper), `Proofs/Erdos/
  CoveringNumber.lean` (`IsTransversal`, `coveringNumber`).

  Mathlib inventory (leandoc 2026-08-05): no hypergraph type;
  `Finset (Finset V)` with a card-r condition is the repo convention
  (Erdos20/Erdos857).  `Set.Intersecting` exists for lattices but the
  Finset-family unfolding below is more direct.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E836

variable {V : Type*} [DecidableEq V]

/-- `Uniform r H`: every edge has exactly `r` vertices. -/
def Uniform (r : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = r

/-- `Intersecting H`: any two edges meet. -/
def Intersecting (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, (e ∩ f).Nonempty

/-- `ProperColoring H c`: no edge is monochromatic under `c`. -/
def ProperColoring {k : ℕ} (H : Finset (Finset V)) (c : V → Fin k) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- `ChromaticThree H`: 3-colorable but not 2-colorable — the standard
    reading of "chromatic number 3" (see fidelity note in the header). -/
def ChromaticThree (H : Finset (Finset V)) : Prop :=
  (∃ c : V → Fin 3, ProperColoring H c) ∧ ¬ ∃ c : V → Fin 2, ProperColoring H c

/-- Satisfiability at the smallest model: the Fano plane (7 points,
    7 lines, 3-uniform, intersecting, χ = 3).  Encoded on `Fin 7` with
    lines of PG(2,2).  -- PROVABLE (decide; 3^7 and 2^7 colorings). -/
def fano : Finset (Finset (Fin 7)) :=
  { {0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6},
    {2, 4, 5} }

set_option maxRecDepth 4096 in
/-- Each of the seven encoded Fano lines has three points. -/
private theorem fano_uniform_certificate : Uniform 3 fano := by
  unfold Uniform fano
  decide

set_option maxRecDepth 4096 in
/-- All 49 ordered pairs of encoded Fano lines meet, including self-pairs. -/
private theorem fano_intersecting_certificate : Intersecting fano := by
  unfold Intersecting fano
  decide

set_option maxRecDepth 4096 in
/-- Distinct encoded Fano lines meet in precisely one point. -/
private theorem fano_distinct_intersection_certificate :
    ∀ e ∈ fano, ∀ f ∈ fano, e ≠ f → (e ∩ f).card = 1 := by
  decide

set_option maxRecDepth 4096 in
/-- The explicit coloring with colors 2,1,1,0,0,0,0 is proper. -/
private theorem fano_three_coloring_certificate :
    ProperColoring fano (![2, 1, 1, 0, 0, 0, 0] : Fin 7 → Fin 3) := by
  unfold ProperColoring fano
  decide

set_option maxRecDepth 4096 in
/-- None of the 128 binary assignments is a proper Fano coloring. -/
private theorem fano_binary_certificate :
    ∀ a b c d e f g : Fin 2,
      ¬ ProperColoring fano (![a, b, c, d, e, f, g] : Fin 7 → Fin 2) := by
  unfold ProperColoring fano
  decide

/-- Every function on the seven points is represented by its seven values. -/
private theorem fano_coloring_values (c : Fin 7 → Fin 2) :
    (![c 0, c 1, c 2, c 3, c 4, c 5, c 6] : Fin 7 → Fin 2) = c := by
  funext x
  fin_cases x <;> rfl

/-- The binary certificate excludes an arbitrary two-coloring. -/
private theorem fano_not_two_colorable :
    ¬ ∃ c : Fin 7 → Fin 2, ProperColoring fano c := by
  rintro ⟨c, hc⟩
  have hbad := fano_binary_certificate (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
  rw [fano_coloring_values c] at hbad
  exact hbad hc

example : Uniform 3 fano ∧ Intersecting fano ∧ ChromaticThree fano := by
  refine ⟨fano_uniform_certificate, fano_intersecting_certificate, ?_⟩
  exact ⟨⟨![2, 1, 1, 0, 0, 0, 0], fano_three_coloring_certificate⟩,
    fano_not_two_colorable⟩

/-- **Erdős #836, first question — REFUTED by Alon** (DB remarks): it is
    NOT true that every intersecting 3-chromatic `r`-uniform hypergraph
    has `O(r²)` vertices; Alon's construction has `≍ 4^r/√r` vertices.
    Archived as the negated universal: for every constant `C` there is
    an `r` and a witness family on more than `C·r²` (indeed
    exponentially many) supported vertices.

    Formalization: the support (vertex set) of `H` is `H.sup id`; the
    witness lives on `Fin M` for a large `M`.  Alon's construction is
    fully explicit (subsets of `X` of size `r` plus partition-markers),
    so this is a *constructive* refutation — but the chromatic and
    intersecting checks for general `r` need real combinatorics, not
    `decide`.  Effort M–L. -/
theorem first_question_refuted :
    ∀ C : ℕ, ∃ (r M : ℕ) (H : Finset (Finset (Fin M))),
      2 ≤ r ∧ Uniform r H ∧ Intersecting H ∧ ChromaticThree H ∧
      C * r ^ 2 < (H.sup id).card := by
  sorry

/-- **Erdős–Lovász intersection theorem** (ErLo75) — the concrete
    Tier-UA target: two edges must meet in `≫ r / log r` vertices.
    Stated with an explicit constant existential over ℝ.

    Proof sketch (attack plan): from [ErLo75] — if all pairwise
    intersections are small, a random 2-coloring argument 2-colors the
    hypergraph, contradicting `ChromaticThree`.  The counting is the
    same genre as the repo's ErdosLovasz g(k) work; the probabilistic
    step is a finite union bound over edges (rational arithmetic, no
    measure theory).  Effort M. -/
theorem erdos_lovasz_intersection :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 3 ≤ r → ∀ (M : ℕ)
      (H : Finset (Finset (Fin M))),
      Uniform r H → Intersecting H → ChromaticThree H →
      ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧
        c * (r : ℝ) / Real.log r ≤ ((e ∩ f).card : ℝ) := by
  sorry

/-- **Second question (status uncertain)**: must two edges meet in
    `≫ r` vertices?  A 2026 AI-assisted proof is claimed in the DB
    comments (Liam Price / GPT-5.5 Pro, "standard check found no
    issues", noted as possibly folklore) but the DB status is still
    open.  Archived. -/
theorem second_question :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 3 ≤ r → ∀ (M : ℕ)
      (H : Finset (Finset (Fin M))),
      Uniform r H → Intersecting H → ChromaticThree H →
      ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * (r : ℝ) ≤ ((e ∩ f).card : ℝ) := by
  sorry

/-- Fano sanity for the intersection sizes: all pairs of distinct Fano
    lines meet in exactly one point — so `r − 1 = 2`-point intersections
    are NOT forced (the DB's Fano remark).  -- PROVABLE (decide). -/
example : ∀ e ∈ fano, ∀ f ∈ fano, e ≠ f → (e ∩ f).card = 1 := by
  exact fano_distinct_intersection_certificate

end ErdosCandidates.E836

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - DB statement matches file header verbatim.
   - ChromaticThree (3-colorable AND not 2-colorable) vs DB parenthetical (only states
     3-colorability): the file's fidelity note is honest and the formalization is
     defensible.  The DB parenthetical is sloppy; [ErLo75] is titled "Problems and
     results on 3-chromatic hypergraphs" where "3-chromatic" means chi = 3 exactly.
     The file's choice is correct.
   - FLAG (minor): ProperColoring requires existence of two vertices with different
     colors in each edge.  For edges of size >= 2 this is equivalent to "not
     monochromatic".  For empty or singleton edges, the existential witnesses would
     fail vacuously (empty edge: no x ∈ e) or trivially (singleton: no y ∈ e with
     c x ≠ c y).  Since Uniform r H with r ≥ 2 excludes these cases, the def is
     safe in context but not self-guarding.
   - Fano plane encoding verified: all 7 lines are size 3 (3-uniform), all pairs
     intersect in exactly 1 point, not 2-colorable (exhaustive 2^7 check), 3-colorable
     (exhaustive 3^7 check).
   - Alon refutation: first_question_refuted correctly states the negation (∀ C, ∃ r M H
     with C*r^2 < |support|).  DB confirms Alon's construction with ~4^r/sqrt(r) vertices.
   - Erdos-Lovasz intersection theorem: r/(log r) bound matches DB ("two edges which
     meet in >> r/log r many vertices").  The existential constant formulation is standard.
   - Second question status: file correctly marks as "status uncertain" citing the
     unreviewed GPT-5.5 Pro claim; DB status remains open.  Appropriate caution.
   - The Intersecting def allows e = f (self-intersection), which is harmless (any set
     intersects itself).
-/
