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

-/
import Mathlib
import Combinatorics.ChordalBasics
import Combinatorics.SplitGraphCliqueLowerBound

set_option autoImplicit false

namespace ErdosCandidates.E81

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ground truth: complete graphs are chordal. -/
example : Chordal (⊤ : SimpleGraph (Fin 5)) := chordal_top_fin5

/-- Non-degeneracy: the four-cycle is not chordal. -/
example : ¬ Chordal (cycleGraph 4) := not_chordal_cycleGraph_four

/-- Satisfiability: the single-triangle partition of the complete graph on three vertices. -/
example : CliqueEdgePartition (⊤ : SimpleGraph (Fin 3))
    {(Finset.univ : Finset (Fin 3))} := cliqueEdgePartition_top_fin3

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
    this restatement is for in-repo reference only.

    Parent primary-source inspection: Woett/Lean-files revision
    0dd69298bc5870970257f002ed376ac35aa8fa8c, ErdosProblem81.lean,
    theorem Erdos81.erdos81. That source uses walk-based IsChordal and
    an infimum clique-partition count (`cp = sInf`); a bridge to
    the induced-cycle and explicit-family definitions here remains unpaid.
    The external source has not been compiled or axiom-audited locally;
    this archive statement remains admitted, not imported or implemented. -/
theorem eoz_woett_bound (n : ℕ) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : Chordal G) :
    ∃ P : Finset (Finset (Fin n)),
      CliqueEdgePartition G P ∧
      (P.card : ℚ) ≤ (1 / 4 - 1 / 133) * n ^ 2 := by
  sorry

/-- **Existential chordal lower bound**, realized by the complete split graph
    whose clique side consists of the vertices with value below `n / 3`.
    With `C = 2`, every clique edge partition of this explicit chordal witness
    satisfies the original quadratic lower bound. This is an in-repo proof;
    it does not certify fidelity to any external formalization or attribution. -/
theorem sharpness_split_witness :
    ∃ C : ℕ, ∀ n : ℕ, 3 ≤ n →
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        Chordal G ∧
        ∀ P : Finset (Finset (Fin n)), CliqueEdgePartition G P →
          n ^ 2 ≤ 6 * P.card + C * n := by
  exact ⟨2, splitGraph_sharpness_witness⟩

end ErdosCandidates.E81

/- VERIFICATION STATUS
   The three basic examples are kernel checked via Combinatorics.ChordalBasics.
   The two upper-bound research targets remain admitted. The original
   existential sharpness target is kernel checked with C = 2 via
   Combinatorics.SplitGraphCliqueLowerBound, using the explicit split graph
   with clique side {x : Fin n | x.val < n / 3}.
   External attribution and source-fidelity certification remain separate.
   The external Woett primary source was inspected at revision
   0dd69298bc5870970257f002ed376ac35aa8fa8c. Its representation bridge and local
   external compilation and axiom audit remain unpaid.
   This is not a whole-archive source-fidelity certification.
-/
