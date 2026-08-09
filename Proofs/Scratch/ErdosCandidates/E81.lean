/-
  Erdős Problem #81 — clique partitions of chordal graphs.
  Status: open.  Tier B archive target.

  Verbatim statement (`goof erdos fetch 81`, pulled 2026-08-05):

    "Let $G$ be a chordal graph on $n$ vertices - that is, $G$ has no
    induced cycles of length greater than $3$. Can the edges of $G$ be
    partitioned into $n^2/6+O(n)$ many cliques?"

  DB remarks: Erdős–Ordman–Zalcstein [EOZ93] proved an upper bound of
  (1/4 − ε)n² cliques (very small ε).  Lower-bound witness: all edges
  between a K_{n/3} and an empty 2n/3-set need n²/6 + O(n) cliques.
  Split graphs (clique ⊎ independent set): Chen–Erdős–Ordman [CEO94]
  give 3n²/16 + O(n).  Comment (Woett, Jun 2026): an explicit
  (1/4 − 1/133)n² bound for chordal graphs with n ≥ 3 is ALREADY
  FORMALIZED in Lean externally
  (github.com/Woett/Lean-files/ErdosProblem81.lean, via ChatGPT 5.5
  Pro + Aristotle) — check that repo before duplicating anything.

  Mathlib inventory (leandoc 2026-08-05): `SimpleGraph.IsClique`,
  `SimpleGraph.edgeFinset`; NO chordality predicate (leandoc miss
  "chordal") and no induced-cycle API — the def below goes through
  induced subgraphs on vertex subsets via `SimpleGraph.induce` and
  graph isomorphism to `cycleGraph m`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E81

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Chordal G`: no induced cycle of length greater than 3 — for every
    vertex subset `s` of size `m ≥ 4`, the induced subgraph on `s` is
    not isomorphic to the `m`-cycle.  (Fresh def; leandoc confirms no
    Mathlib chordality.) -/
def Chordal (G : SimpleGraph V) : Prop :=
  ∀ (s : Finset V), 4 ≤ s.card →
    IsEmpty ((G.induce (s : Set V)) ≃g cycleGraph s.card)

/-- Ground truth: complete graphs are chordal (no induced C_m for
    m ≥ 4 — every 4-subset induces K₄ ≇ C₄).  -- PROVABLE. -/
example : Chordal (⊤ : SimpleGraph (Fin 5)) := by
  sorry

/-- Non-degeneracy: `C₄` itself is not chordal.
    -- PROVABLE (the full vertex set induces C₄). -/
example : ¬ Chordal (cycleGraph 4) := by
  sorry

/-- `CliqueEdgePartition G P`: `P` is a family of vertex-cliques of `G`
    such that every edge of `G` lies inside exactly one member of `P`.
    ("Partition of the edges into cliques"; members of size ≤ 1 carry
    no edges and are excluded for cleanliness.) -/
def CliqueEdgePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ s ∈ P, G.IsClique (s : Set V) ∧ 2 ≤ s.card) ∧
  ∀ e ∈ G.edgeFinset, ∃! s, s ∈ P ∧ ∀ v ∈ e, v ∈ s

/-- Satisfiability: the single-triangle partition of `K₃`.
    -- PROVABLE (decide). -/
example : CliqueEdgePartition (⊤ : SimpleGraph (Fin 3))
    {(Finset.univ : Finset (Fin 3))} := by
  sorry

/-- **Erdős #81 (OPEN)**: every chordal graph on `n` vertices admits a
    clique edge-partition into at most `n²/6 + C·n` cliques, for some
    absolute constant `C`.

    Source text: "Can the edges of $G$ be partitioned into
    $n^2/6+O(n)$ many cliques?"  Stated multiplicatively:
    `6·|P| ≤ n² + C·n`. -/
theorem erdos_81 :
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      Chordal G →
      ∃ P : Finset (Finset (Fin n)),
        CliqueEdgePartition G P ∧ 6 * P.card ≤ n ^ 2 + C * n := by
  sorry

/-- **EOZ / Woett-formalized bound**, archived here as the known slice:
    chordal graphs on `n ≥ 3` vertices partition into at most
    `(1/4 − 1/133)·n²` cliques.  ⚠ An external Lean formalization
    already exists (Woett, Jun 2026) — cite, do not duplicate;
    this restatement is for in-repo reference only. -/
theorem eoz_woett_bound (n : ℕ) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : Chordal G) :
    ∃ P : Finset (Finset (Fin n)),
      CliqueEdgePartition G P ∧
      (P.card : ℚ) ≤ (1 / 4 - 1 / 133) * n ^ 2 := by
  sorry

/-- **Sharpness witness family** (EOZ93): the complete split graph
    (all edges between a clique on ⌈n/3⌉ vertices and an independent
    set on the rest, plus the clique edges) needs `n²/6 + O(n)`
    cliques — the natural provable slice for the lower-bound side.
    Stated for the witness at a general `n` with the explicit
    `n²/6 − C·n` lower bound on every partition. -/
theorem sharpness_split_witness :
    ∃ C : ℕ, ∀ n : ℕ, 3 ≤ n →
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        Chordal G ∧
        ∀ P : Finset (Finset (Fin n)), CliqueEdgePartition G P →
          n ^ 2 ≤ 6 * P.card + C * n := by
  sorry

end ErdosCandidates.E81

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB exactly.
   - Chordal def (no induced C_m for m>=4 over all subsets of size m)
     is faithful to "no induced cycles of length greater than 3".
   - CliqueEdgePartition correctly encodes edge partition into cliques
     (each edge in exactly one clique, each part is a clique of size >=2).
   - Main conjecture restated as 6*|P| <= n^2 + C*n, faithful to
     n^2/6 + O(n) with the multiplicative clearing.
   - EOZ upper bound (1/4 - epsilon)n^2 matches DB.
   - Woett formalization (1/4 - 1/133)n^2 for n>=3 matches DB comment
     (Woett, 19 Jun 2026); correctly flagged as comment-sourced and
     external (github.com/Woett/Lean-files).  Attribution to ChatGPT 5.5
     Pro + Aristotle matches the comment.
   - CEO split graph bound 3n^2/16 + O(n) matches DB.
   - Sharpness witness (K_{n/3} + empty 2n/3) matches DB lower bound
     description.
   - No Mathlib chordality predicate confirmed.
-/
