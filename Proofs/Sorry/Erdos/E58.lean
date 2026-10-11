/-
  Erdős Problem #58 — chromatic number versus number of odd cycle lengths.
  Status: proved (Gyárfás 1992).  Tier A proof target.

  Verbatim statement (`goof erdos fetch 58`, pulled 2026-08-05):

    "If $G$ is a graph which contains odd cycles of $\leq k$ different
    lengths then $\chi(G)\leq 2k+2$, with equality if and only if $G$
    contains $K_{2k+2}$."

  DB remarks: conjectured by Bollobás–Erdős; k = 1 confirmed by
  Bollobás–Shelah; proved by Gyárfás [Gy92], who proved the stronger
  result that a 2-connected such G is either K_{2k+2} or has a vertex of
  degree ≤ 2k.  Strengthening by Gao–Huo–Ma [GaHuMa21]: χ(G) ≥ 2k+3
  forces cycles of k+1 consecutive odd lengths.

  Mathlib inventory (leandoc 2026-08-05):
  * `SimpleGraph.chromaticNumber : ℕ∞` (Coloring/Vertex.lean);
  * `SimpleGraph.Walk.IsCycle`, `Walk.length` for cycle lengths;
  * `SimpleGraph.CliqueFree` / `IsNClique` for the K_{2k+2} condition;
  * `Set.Finite`, `Set.ncard` for "≤ k different lengths".
  No off-the-shelf odd-cycle-spectrum machinery; the definition layer
  below is fresh.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E58

open SimpleGraph

variable {V : Type*}

/-- The set of lengths of odd cycles of `G` — the "odd cycle spectrum".
    A length `ℓ` is in the spectrum iff some cycle of `G` has odd length
    `ℓ`. -/
def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  {ℓ : ℕ | Odd ℓ ∧ ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = ℓ}

/-- Ground truth: the odd cycle spectrum of a triangle is `{3}`.
    -- PROVABLE (the only cycles of `K₃` have length 3). -/
example : oddCycleLengths (⊤ : SimpleGraph (Fin 3)) = {3} := by
  sorry

/-- Ground truth: bipartite graphs have empty odd cycle spectrum —
    e.g. `K₂`.  Guards the k = 0 edge of the statement: with no odd
    cycles the bound reads χ ≤ 2, which is the bipartite case.
    -- PROVABLE. -/
example : oddCycleLengths (⊤ : SimpleGraph (Fin 2)) = ∅ := by
  sorry

/-- **Erdős #58, Gyárfás's theorem, headline bound** (Gy92): if a finite
    graph has at most `k` different odd cycle lengths, then
    `χ(G) ≤ 2k + 2`.

    Source text: "If $G$ is a graph which contains odd cycles of $\leq k$
    different lengths then $\chi(G)\leq 2k+2$..."

    Formalization notes: `chromaticNumber : ℕ∞`, so the bound is stated
    in `ℕ∞`; `V` finite keeps χ finite.  "≤ k different lengths" =
    `(oddCycleLengths G).Finite ∧ ncard ≤ k` — for finite `V` the
    spectrum is automatically finite, so we state just the `ncard`
    bound with `Set.ncard` (which is 0 for infinite sets; harmless here
    since the set is finite, but the `Finite` conjunct is kept to guard
    the degenerate reading per STYLE.md).

    Proof sketch (attack plan): Gyárfás's induction: reduce to a
    2-connected block (χ is the max over blocks; block decomposition is
    the missing Mathlib piece — expect to prove a weak form: induction
    on vertices, deleting a vertex of degree ≤ 2k+1).  Core lemma: a
    2-connected graph with min degree ≥ 2k+1 that is not K_{2k+2} has
    odd cycles of > k lengths, proved via a DFS/longest-path argument
    producing cycles of many different parities.  First slice to
    attempt: `k = 1` (Bollobás–Shelah): one odd cycle length forces
    χ ≤ 4.  Mathlib tools: `chromaticNumber_le_iff_colorable`,
    `Colorable` monotonicity, strong induction on `Fintype.card V`.
    Effort M (headline) per candidates audit. -/
theorem gyarfas_chromatic_bound [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hfin : (oddCycleLengths G).Finite)
    (hk : (oddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ) := by
  sorry

/-- **Erdős #58, equality case** (Gy92): equality `χ(G) = 2k + 2` holds
    iff `G` contains `K_{2k+2}` (as a subgraph, i.e. `G` is not
    `(2k+2)`-clique-free).  The forward direction is the hard one; the
    backward direction is the trivial `χ ≥ clique number` plus the
    headline bound.  Effort L per candidates audit — sorry'd separately
    from the headline so the lane can land the bound first. -/
theorem gyarfas_equality_iff [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hfin : (oddCycleLengths G).Finite)
    (hk : (oddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber = (2 * k + 2 : ℕ) ↔ ¬ G.CliqueFree (2 * k + 2) := by
  sorry

/-- Satisfiability of the equality case at `k = 1`: `K₄` has odd cycle
    spectrum `{3}` (one length) and `χ(K₄) = 4 = 2·1 + 2`.
    -- PROVABLE (decide-scale + `chromaticNumber_top`). -/
example :
    (oddCycleLengths (⊤ : SimpleGraph (Fin 4))).ncard = 1 ∧
    (⊤ : SimpleGraph (Fin 4)).chromaticNumber = (4 : ℕ) := by
  sorry

/-- Sanity for the `k = 1` slice (Bollobás–Shelah): a 5-cycle has one
    odd cycle length and χ(C₅) = 3 ≤ 4.
    -- PROVABLE (`chromaticNumber_cycleGraph_of_odd` exists in Mathlib,
    leandoc hit in Coloring/Constructions.lean). -/
example : (cycleGraph 5).chromaticNumber ≤ (4 : ℕ) := by
  sorry

end ErdosCandidates.E58

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim.
   - Solver attribution Gyarfas [Gy92] matches DB.
   - `oddCycleLengths` definition is faithful: set of lengths l such that l is odd and some cycle of G has length l.
   - `chromaticNumber : ℕ∞` correctly handled via cast `(2 * k + 2 : ℕ)` to `ℕ∞`.
   - Equality case `χ = 2k+2 ↔ ¬CliqueFree (2k+2)` faithfully translates "iff G contains K_{2k+2}": ¬CliqueFree n = "has an n-clique" = "contains K_n as subgraph".
   - k=0 edge: no odd cycles means χ ≤ 2, the bipartite bound. Correct (bipartite ↔ no odd cycles).
   - K₄ satisfiability: odd cycle spectrum = {3} (only triangles), χ(K₄) = 4 = 2*1+2. Correct.
   - C₅ sanity: one odd cycle length (5), χ(C₅) = 3 ≤ 4. Correct.
   - `Set.ncard` for "≤ k different lengths" is appropriate; finite guard `hfin` included.
   - No Mathlib definition for odd-cycle-spectrum exists; fresh `oddCycleLengths` is justified.
-/
