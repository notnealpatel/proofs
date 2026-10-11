/-
  Erdős Problem #86 — C₄-free subgraphs of the hypercube.
  Status: open; $100.  Tier B archive target with certificate layer.

  Verbatim statement (`goof erdos fetch 86`, pulled 2026-08-05):

    "Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has
    $2^n$ vertices and $n2^{n-1}$ edges). Is it true that every subgraph
    of $Q_n$ with
    \[\geq \left(\frac{1}{2}+o(1)\right)n2^{n-1}\]
    many edges contains a $C_4$?"

  DB remarks: with f(n) = max C₄-free edge count, the conjecture is
  f(n) ≤ (1/2 + o(1))·n·2^{n-1}.  Erdős [Er91]: f(n) ≥ (1/2 + c/n)·n·2^{n-1};
  Brass–Harborth–Nienborg [BHN95]: f(n) ≥ (1/2 + c/√n)·n·2^{n-1}.
  Balogh–Hu–Lidický–Liu [BHLL14]: f(n) ≤ 0.6068·n·2^{n-1}; Baber
  [Ba12b]: f(n) ≤ 0.60318·n·2^{n-1}.  Comment (rafalwrona, May 2026,
  comment-sourced): explicit C₄-free edge-list certificates for Q₉–Q₁₅
  (e.g. Q₉: 1505 edges), verified by exhaustive 4-cycle enumeration.

  OEIS anchor: A245762.

  Mathlib inventory (leandoc 2026-08-05): no hypercube graph
  (leandoc miss "hypercube"); `SimpleGraph.cycleGraph`,
  `SimpleGraph.Free` (`¬ A ⊑ B`, Copy.lean) for C₄-containment;
  `SimpleGraph.edgeFinset.card` for edge counts.  Q_n defined fresh
  below on `Fin n → Bool`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E86

open SimpleGraph

/-- The `n`-dimensional hypercube graph on `Fin n → Bool`: adjacent iff
    the points differ in exactly one coordinate.  (Fresh def; leandoc
    confirms no Mathlib hypercube graph.  `Finset.filter` over `univ`
    keeps it decidable.) -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := (Finset.univ.filter (fun i => x i ≠ y i)).card = 1
  symm := by
    intro x y h
    simpa [ne_comm] using h
  loopless := by
    intro x h
    simp at h

/-- Ground truth: `Q_n` has `2^n` vertices and `n·2^{n-1}` edges (the
    DB's own parenthetical).  -- PROVABLE (double counting; or decide
    for n ≤ 3). -/
theorem hypercube_card_verts (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  sorry

theorem hypercube_card_edges (n : ℕ) [DecidableRel (hypercube n).Adj] :
    (hypercube n).edgeFinset.card = n * 2 ^ (n - 1) := by
  sorry

/-- `C4Free H`: `H` contains no 4-cycle, via Mathlib's `Free`
    (no copy of `cycleGraph 4`). -/
def C4Free {V : Type*} (H : SimpleGraph V) : Prop :=
  (cycleGraph 4).Free H

/-- Sanity: `Q_2` is itself a 4-cycle, so `Q_2` is NOT C₄-free, and
    deleting any edge of `Q_2` leaves a C₄-free graph with 3 edges.
    -- PROVABLE (decide-scale). -/
example : ¬ C4Free (hypercube 2) := by
  sorry

/-- `maxC4FreeEdges n`: the extremal count `f(n)` — the largest number
    of edges of a C₄-free subgraph of `Q_n`.  Encoded as a sup over
    subgraphs `H ≤ hypercube n` (classical choice for the filter). -/
open scoped Classical in
noncomputable def maxC4FreeEdges (n : ℕ) : ℕ :=
  Finset.sup
    (Finset.univ.filter
      (fun H : SimpleGraph (Fin n → Bool) => H ≤ hypercube n ∧ C4Free H))
    (fun H => H.edgeFinset.card)

/-- **Erdős #86 (OPEN, $100)**: `f(n) ≤ (1/2 + o(1))·n·2^{n-1}` —
    every subgraph of `Q_n` with `(1/2 + ε)·n·2^{n-1}` edges contains a
    C₄, for every `ε > 0` and `n` large.

    Source text: "Is it true that every subgraph of $Q_n$ with
    $\geq (\frac{1}{2}+o(1))n2^{n-1}$ many edges contains a $C_4$?"

    Best known: `f(n) ≤ 0.60318·n·2^{n-1}` (Baber, flag algebras) —
    the flag-algebra certificate is a large SDP, an interesting but
    heavy verification target.  Archived. -/
theorem erdos_86 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (maxC4FreeEdges n : ℝ) ≤ (1 / 2 + ε) * n * 2 ^ (n - 1) := by
  sorry

/-- **BHN lower bound** (BHN95), archived: for some `c > 0` and all
    large `n`, `(1/2 + c/√n)·n·2^{n-1} ≤ f(n)`.  The construction is
    explicit (layered edge selection); a fully explicit finite slice is
    the certificate layer below. -/
theorem bhn_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 / 2 + c / Real.sqrt n) * n * 2 ^ (n - 1) ≤ (maxC4FreeEdges n : ℝ) := by
  sorry

/-- **Certificate layer (the repo lane)**: `f(9) ≥ 1505` — an explicit
    C₄-free subgraph of `Q₉` with 1505 edges exists (rafalwrona's
    edge-list certificate, comment-sourced; SHA-pinned JSON in the
    linked repo).  Verification = C₄-freeness of an explicit edge list:
    `native_decide` territory (4608 potential C₄s in Q₉ per the
    comment's table).  Fetch the edge list before attempting.
    -- PROVABLE-in-principle (native_decide). -/
theorem certificate_q9 : 1505 ≤ maxC4FreeEdges 9 := by
  sorry

/-- Small exact value sanity: `f(2) = 3` (drop any edge of the single
    4-cycle).  -- PROVABLE (decide over subgraphs of Q₂, 2⁴ edge
    subsets).  Pins `maxC4FreeEdges` against off-by-one in the sup
    encoding. -/
theorem maxC4FreeEdges_two : maxC4FreeEdges 2 = 3 := by
  sorry

end ErdosCandidates.E86

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB exactly.
   - Hypercube graph fresh def confirmed necessary: Mathlib has no
     SimpleGraph hypercube (grep hit only HalesJewett combinatorial
     hypercubes, not graph-theoretic).
   - Q_n vertex count 2^n and edge count n*2^(n-1) match DB parenthetical.
   - C4Free uses (cycleGraph 4).Free H, which expands to !(cycleGraph 4 <= H)
     i.e. "H does not contain a copy of C4" -- correct direction confirmed
     from Copy.lean:372.
   - f(2) = 3: Q2 is C4 itself (4 edges); deleting any edge gives 3 C4-free
     edges.  Correct.
   - Q9 certificate 1505 edges matches rafalwrona comment table exactly.
   - rafalwrona comment correctly flagged as comment-sourced (May 2026).
   - Upper bounds: Baber 0.60318 and BHLL 0.6068 match DB and comment.
   - Lower bounds: Erdos c/n and BHN c/sqrt(n) match DB section text.
   - OEIS A245762 anchor noted.
-/
