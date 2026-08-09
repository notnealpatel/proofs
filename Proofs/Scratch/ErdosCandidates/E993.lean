/-
  Erdős Problem #993 — unimodality of the independent-set sequence of
  trees and forests.
  Status: falsifiable (open for trees; false for general graphs by
  AMSE 1987).  Tier B archive target with a computational sweep lane.

  Verbatim statement (`goof erdos fetch 993`, pulled 2026-08-05):

    "The independent set sequence of any tree or forest is unimodal.

    In other words, if $i_k(G)$ counts the number of independent sets of
    vertices of size $k$ in a graph $G$, and $T$ is any tree or forest,
    then for some $m\geq 0$
    $$i_{0}(T)\leq i_{1}(T)\leq\cdots\leq i_{m}(T)\geq i_{m+1}(T)\geq
    i_{m+2}(T)\geq\cdots.$$"

  DB remarks: question of Alavi–Malde–Schwenk–Erdős [AMSE87], who showed
  unimodality is false for general graphs (every inequality pattern is
  achieved).  Comment thread (2026): verified for all trees on ≤ 29
  vertices (JakeMallen, BrettRey — 5.4·10⁹ trees at n = 29, zero
  failures); PatternBoost sampling to 101 vertices; log-concavity DOES
  fail from 26 vertices (Kadrawi–Levit 2023), and Hoggar's theorem
  (products of log-concave sequences) reduces the forest case to
  non-log-concave tree components (Will Blair's comment).

  Mathlib inventory (leandoc 2026-08-05):
  * independent sets of size k = k-cliques of the complement:
    `SimpleGraph.cliqueFinset` on `Gᶜ` (DecidableRel required);
  * `SimpleGraph.IsTree` (structure, Acyclic.lean), `IsAcyclic` for
    forests;
  * no unimodality predicate for ℕ-sequences (leandoc miss "unimodal
    sequence") — fresh def below.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E993

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `indepCount G k`: the number of independent vertex sets of size `k`
    in `G` — realized as `k`-cliques of the complement, reusing
    Mathlib's `cliqueFinset`. -/
def indepCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ((Gᶜ).cliqueFinset k).card

/-- `Unimodal a`: the ℕ-sequence rises to some peak `m` then falls.
    (Fresh def; leandoc confirms no Mathlib unimodality predicate.) -/
def Unimodal (a : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, (∀ i j, i ≤ j → j ≤ m → a i ≤ a j) ∧
    (∀ i j, m ≤ i → i ≤ j → a j ≤ a i)

/-- Ground truth: the path P₄ (4 vertices, 3 edges) has independent-set
    sequence 1, 4, 3, 0, 0, … — unimodal with peak m = 1.  (Corrected
    per review: no 3 vertices of P₄ are pairwise non-adjacent, so
    i₃ = 0.)  -- PROVABLE (decide on `pathGraph 4` — Mathlib has
    `SimpleGraph.pathGraph`). -/
example :
    indepCount (pathGraph 4) 0 = 1 ∧ indepCount (pathGraph 4) 1 = 4 ∧
    indepCount (pathGraph 4) 2 = 3 ∧ indepCount (pathGraph 4) 3 = 0 := by
  sorry

/-- **Erdős #993, tree case (OPEN — the conjecture)**: the
    independent-set sequence of any finite tree is unimodal.

    Sanity-scale evidence: verified for all trees on ≤ 29 vertices
    (comment-sourced computations, 2026); the repo lane here is a
    `native_decide` unimodality sweep over all trees on ≤ 15 vertices
    (either outcome is progress — a counterexample resolves #993, a
    clean sweep is a verified partial result).  Note: exhaustive
    enumeration of trees needs a verified generator (Prüfer sequences:
    `Fintype` on `Fin (n-2) → Fin n` codes, decode via Mathlib-free
    construction) — the natural infrastructure piece. -/
theorem tree_unimodal (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.IsTree) :
    Unimodal (indepCount G) := by
  sorry

/-- **Forest reduction (Hoggar route)**: the independence polynomial of
    a disjoint union is the product, and products of log-concave
    positive sequences are log-concave (Hoggar 1974); a forest whose
    tree components all have log-concave sequences has unimodal
    sequence.  Stated as the polynomial product identity — the
    formalizable slice feeding the Blair reduction.
    `G ⊔ H` on `V ⊕ W` is `SimpleGraph.sum`? — Mathlib spells disjoint
    union of graphs as `G ⊕g H`?? (check: `SimpleGraph.disjUnion`-like
    API; leandoc probe needed at campaign start).  Stated here via a
    sum over antidiagonal. -/
theorem indepCount_disjoint_union {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) :
    ∃ (U : SimpleGraph (V ⊕ W)) (_ : DecidableRel U.Adj),
      indepCount U k =
        ∑ p ∈ Finset.antidiagonal k, indepCount G p.1 * indepCount H p.2 := by
  sorry

/-- **AMSE 1987 negative result for general graphs**, archived: there
    is a finite graph whose independent-set sequence is NOT unimodal.
    (Every inequality pattern is realizable; the standard small witness
    is K_m plus isolated-vertex tricks — e.g. `K₄ ⊔ (3·K₁)`-shaped
    graphs give 1, 7, 3, ... valleys.  Probe for the smallest witness,
    then `decide`.)  -- PROVABLE (decide once the witness is pinned). -/
theorem amse_general_graphs_fail :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      ¬ Unimodal (indepCount G) := by
  sorry

/-- Sweep target for the repo lane: every tree on ≤ 15 vertices has
    unimodal independent-set sequence.  -- PROVABLE-in-principle
    (native_decide over Prüfer codes; ~10¹⁴ naive at n = 15 is too
    big — restrict to n ≤ 10 (10⁸ codes) for the first landing, or
    quotient by isomorphism offline). -/
theorem tree_sweep_small (n : ℕ) (hn : n ≤ 10) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hT : G.IsTree) :
    Unimodal (indepCount G) := by
  sorry

end ErdosCandidates.E993

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: FLAG
   - Statement matches source verbatim. AMSE87 attribution correct.
   - Mathlib inventory verified: SimpleGraph.pathGraph exists (Hasse.lean:108),
     SimpleGraph.cliqueFinset exists (Clique.lean:793). Claims correct.
   - FLAG (arithmetic error): the ground-truth example claims
       indepCount (pathGraph 4) 3 = 1
     but the correct value is 0. P4 has vertices {0,1,2,3} with edges {01,12,23};
     no triple of vertices is mutually non-adjacent. The independent-set sequence
     of P4 is 1, 4, 3, 0, 0, ... not 1, 4, 3, 1, 0, ... The example statement
     must be corrected to `indepCount (pathGraph 4) 3 = 0`.
   - Unimodal def is non-standard in one respect: it quantifies over all j
     (including beyond the vertex count), but since indepCount returns 0 for
     k > |V|, the tail is constant-0 and does not break unimodality. Acceptable.
   - Comment-sourced claims (JakeMallen/BrettRey n<=29, Kadrawi-Levit LC failures,
     Will Blair Hoggar reduction, PatternBoost) correctly flagged as comment-sourced.
   - indepCount via complement cliques is mathematically correct.
-/

/- RESOLUTION (prover, 2026-08-05): the FLAG above (indepCount
   (pathGraph 4) 3 = 1 vs correct value 0) was fixed in the example
   statement and docstring immediately after review; P₄'s sequence is
   1, 4, 3, 0.  Effective verdict after fix: PASS. -/
