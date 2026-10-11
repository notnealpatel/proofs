/-
  Erdős Problem #548 — the Erdős–Sós conjecture on trees.
  Status: falsifiable (open).  Tier UB archive target.

  Verbatim statement (`goof erdos fetch 548`, pulled 2026-08-05):

    "Let $n\geq k+1$. Every graph on $n$ vertices with at least
    $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices."

  DB remarks: Erdős–Sós; the companion forest version has threshold
  max(C(2k−1,2)+1, (k−1)n−(k−1)²+C(k−1,2)+1) (Erdős–Gallai for k
  independent edges).  [Er78]: trivial for stars; Erdős–Gallai proved
  the path case.  Easy: n(k−1)+1 edges force every tree on k+1
  vertices.  Partial: girth ≥ 5 hosts (Brandt–Dobson), C₄-free hosts
  (Saclé–Woźniak), complement variants, K_{2,s}-free hosts (Haxell;
  Balasubramanian–Dobson), spiders (Fan–Hong–Liu), k ≤ 9
  (Eaton–Tiner; Tiner–Tomlin), n ∈ {k, …, k+4} hosts.  An announced
  Ajtai–Komlós–Simonovits–Szemerédi proof for large k remains
  unpublished.

  Mathlib inventory: `SimpleGraph.IsTree`, `SimpleGraph.Free`
  (`¬ A ⊑ B`; `A ⊑ B` = A has a copy in B — so "G contains every
  tree" is `T ⊑ G` for all trees T), `edgeFinset.card`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E548

open SimpleGraph

/-- `ContainsAllTrees G k`: `G` contains (a copy of) every tree on
    `k + 1` vertices. -/
def ContainsAllTrees {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T ⊑ G

/-- Ground truth: `K₄` contains both trees on 3 vertices... there is
    only one tree shape on 3 vertices (the path); on 4 vertices there
    are two (path, star) — `K₄` contains all of them (k = 3).
    -- PROVABLE (explicit embeddings). -/
example : ContainsAllTrees (⊤ : SimpleGraph (Fin 4)) 3 := by
  sorry

/-- **Erdős #548, the Erdős–Sós conjecture (OPEN)**: every graph on
    `n ≥ k + 1` vertices with more than `(k−1)n/2` edges contains every
    tree on `k + 1` vertices.

    Source text: "Every graph on $n$ vertices with at least
    $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices."
    Encoded division-free: `(k−1)·n < 2·#edges`, i.e. "#edges >
    (k−1)n/2" — the standard literature form of Erdős–Sós.  Parity
    note (review-corrected): when `(k−1)n` is odd this is ONE EDGE
    WEAKER as a hypothesis than the DB's literal "≥ (k−1)n/2 + 1"
    (which over-rounds); the statement here is the stronger claim and
    is the one the extremal witnesses (disjoint K_k's) are tight
    against.  Archived — serious extremal graph theory; the provable
    fragments are below. -/
theorem erdos_sos (n k : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (k - 1) * n < 2 * G.edgeFinset.card) :
    ContainsAllTrees G k := by
  sorry

/-- **The easy bound** (DB: "easily proved by induction"): `n(k−1)+1`
    edges suffice — i.e. `(k−1)·n < #edges` forces every tree on
    `k+1` vertices.  The genuine first target: induction extracting a
    min-degree-≥ k subgraph (a graph with > n(k−1) edges has a
    subgraph of min degree ≥ k, which greedily embeds every tree on
    k+1 vertices).  Mathlib: `SimpleGraph.minDegree`, greedy embedding
    by strong induction.  Effort M. -/
theorem easy_double_bound (n k : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (k - 1) * n < G.edgeFinset.card) :
    ContainsAllTrees G k := by
  sorry

/-- **The path case (Erdős–Gallai)**, archived-but-plausible: with
    more than `(k−1)n/2` edges, `G` contains the path on `k + 1`
    vertices.  This is the classical Erdős–Gallai path theorem — the
    natural provable slice (effort M–L; the standard proof is a
    longest-path/rotation argument).  `pathGraph (k+1)` is Mathlib's
    path graph. -/
theorem erdos_gallai_path (n k : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (k - 1) * n < 2 * G.edgeFinset.card) :
    pathGraph (k + 1) ⊑ G := by
  sorry

/-- Sharpness sanity: the threshold is tight — a disjoint union of
    `K_k`'s has exactly `(k−1)n/2` edges and contains no tree on
    `k + 1` vertices (every component has only k vertices).  Stated at
    the smallest instance `n = k` (a single `K_k`):
    `K_k` has `(k−1)k/2` edges and no tree on `k+1` vertices embeds.
    -- PROVABLE (embedding would need k+1 distinct vertices). -/
theorem sharpness_kk (k : ℕ) (hk : 1 ≤ k) :
    2 * (⊤ : SimpleGraph (Fin k)).edgeFinset.card = (k - 1) * k ∧
    ¬ ContainsAllTrees (⊤ : SimpleGraph (Fin k)) k := by
  sorry

end ErdosCandidates.E548

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - Statement matches DB verbatim (re-pulled 2026-08-05).
   - FLAG (parity): the division-free encoding `(k-1)*n < 2*edges`
     is equivalent to "more than (k-1)n/2 edges", which matches the
     standard Erdos-Sos conjecture. However, the DB literally says
     "at least (k-1)n/2 + 1 edges". When (k-1)n is odd these differ:
     the file accepts one fewer edge (e.g. k=2 n=3: file needs >= 2
     edges, DB literal needs >= 3). The file's comment "the strict
     form is the faithful reading ... for all parities" is incorrect
     against the literal DB text. The file's theorem is STRONGER
     (weaker hypothesis) than the DB statement for odd (k-1)n.
     Mathematically the standard conjecture IS "more than (k-1)n/2"
     and the file's encoding is the standard one; the DB's "+1" is
     redundant for even parity and overly strong for odd parity.
     Recommend: either tighten to `(k-1)*n + 1 < 2*edges` for literal
     fidelity, or explicitly note the strengthening in the comment.
   - Attributions: Erdos-Gallai path case, Brandt-Dobson girth >= 5,
     Haxell/Balasubramanian-Dobson K_{2,s}-free, Fan-Hong-Liu spiders,
     Eaton-Tiner k <= 8, Tiner-Tomlin k = 9, AKSS announced proof --
     all confirmed against DB comments.
   - Sharpness example (disjoint K_k): correct, extremal has (k-1)k/2
     edges per copy.
-/
