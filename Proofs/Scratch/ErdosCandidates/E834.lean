/-
  Erdős Problem #834 — a 3-critical 3-uniform hypergraph of minimum
  degree 7.
  Status: solved (Li 2025) — YES under chromatic criticality, NO under
  transversal criticality.  Tier C target (seeds a hypergraph lane).

  Verbatim statement (`goof erdos fetch 834`, pulled 2026-08-05):

    "Does there exist a $3$-critical $3$-uniform hypergraph in which
    every vertex has degree $\geq 7$?"

  DB remarks (Erdős–Lovász [ErLo75]): "3-critical" was not specified.
  Two readings: (a) transversal-critical (τ = 3, every edge-deleted
  subhypergraph has a 2-transversal) — Raphael Steiner observed such
  hypergraphs have bounded size, making the problem finite;
  (b) chromatic-critical (χ = 3, deleting any edge or vertex drops χ
  to 2) — the reading endorsed by AlexisOlson's comment (source paper
  context, Abbott–Hare terminology, non-triviality).  Li [Li25,
  arXiv:2512.24850] resolved BOTH: transversal-critical forces a
  vertex of degree ≤ 6; chromatic-critical admits an explicit
  9-vertex construction with min degree 7.

  Repo adjacency: `Proofs/Erdos/CoveringNumber.lean` (`IsTransversal`,
  `coveringNumber`) covers the transversal-side vocabulary;
  `ErdosLovasz.lean` is the same paper's other problem.

  Mathlib inventory: no hypergraph type; `Finset (Finset (Fin 9))`
  convention.  3^9 = 19683 colorings × ≤ C(9,3) edges: criticality
  checking is `decide`/`native_decide` sized once Li's edge list is
  transcribed (it is explicit in [Li25]; fetch before proving).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E834

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `ProperColoring H c`: no edge of `H` is monochromatic under `c`. -/
def ProperColoring {k : ℕ} (H : Finset (Finset V)) (c : V → Fin k) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- `ChromaticallyThreeCritical H`: χ(H) = 3 (3-colorable, not
    2-colorable) and every proper edge- or vertex-deletion is
    2-colorable.  Vertex deletion = restrict to edges avoiding `v`. -/
def ChromaticallyThreeCritical (H : Finset (Finset V)) : Prop :=
  (∃ c : V → Fin 3, ProperColoring H c) ∧
  (¬ ∃ c : V → Fin 2, ProperColoring H c) ∧
  (∀ e ∈ H, ∃ c : V → Fin 2, ProperColoring (H.erase e) c) ∧
  (∀ v : V, ∃ c : V → Fin 2,
    ProperColoring (H.filter (fun e => v ∉ e)) c)

/-- `degree H v`: the number of edges containing `v`. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

/-- Ground truth for the degree def: in the Fano plane every point has
    degree 3.  -- PROVABLE (decide). -/
example :
    degree ({{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6},
      {2,4,5}} : Finset (Finset (Fin 7))) 0 = 3 := by
  sorry

/-- **Erdős #834, chromatic reading — Li's construction** ([Li25]):
    there is a 3-uniform, chromatically 3-critical hypergraph on 9
    vertices with every vertex of degree ≥ 7.

    Source: "Does there exist a $3$-critical $3$-uniform hypergraph in
    which every vertex has degree $\geq 7$?"  Answer YES (chromatic
    criticality).

    Attack: transcribe Li's explicit 9-vertex edge list from
    arXiv:2512.24850 (`goof fetch` the paper into References first),
    then every conjunct is a finite check: uniformity and degrees by
    `decide`; 2-uncolorability is 2⁹ = 512 colorings; 3-colorability
    exhibits one witness; criticality is |H| + 9 more 512-sweeps.
    `native_decide` comfortably; kernel `decide` plausibly.  Effort M
    (transcription + instance wrangling), and it seeds the repo's
    hypergraph lane. -/
theorem li_construction :
    ∃ H : Finset (Finset (Fin 9)),
      (∀ e ∈ H, e.card = 3) ∧
      ChromaticallyThreeCritical H ∧
      ∀ v : Fin 9, 7 ≤ degree H v := by
  sorry

/-- **Li's negative result, transversal reading** ([Li25]): a
    transversal-3-critical 3-uniform hypergraph must have a vertex of
    degree ≤ 6.  Transversal criticality via the repo's
    `IsTransversal`-style vocabulary, inlined here: τ(H) = 3 and
    every single-edge deletion has a 2-transversal.  Archived (Li's
    proof is a finite but nontrivial structural argument; Steiner's
    boundedness observation makes it finitely checkable in
    principle). -/
theorem li_transversal_negative (n : ℕ) (H : Finset (Finset (Fin n)))
    (huni : ∀ e ∈ H, e.card = 3)
    (hτ3 : (∃ T : Finset (Fin n), T.card = 3 ∧
              ∀ e ∈ H, (e ∩ T).Nonempty) ∧
           ¬ ∃ T : Finset (Fin n), T.card = 2 ∧ ∀ e ∈ H, (e ∩ T).Nonempty)
    (hcrit : ∀ e ∈ H, ∃ T : Finset (Fin n), T.card = 2 ∧
              ∀ f ∈ H.erase e, (f ∩ T).Nonempty) :
    ∃ v : Fin n, degree H v ≤ 6 := by
  sorry

/-- Satisfiability of chromatic 3-criticality at a small model: the
    Fano plane is 3-chromatic, and it is edge-critical (deleting any
    line leaves a 2-colorable hypergraph).  (Vertex-criticality of
    Fano: deleting a point leaves 4 lines on 6 points — 2-colorable.)
    So `ChromaticallyThreeCritical fano` — the definition is
    non-vacuous.  -- PROVABLE (decide; 2⁷ and 3⁷ sweeps). -/
example : ChromaticallyThreeCritical
    ({{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6},
      {2,4,5}} : Finset (Finset (Fin 7))) := by
  sorry

end ErdosCandidates.E834

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 834` exactly.
   - Both criticality readings (transversal and chromatic) faithfully described per DB.
   - Steiner bounded-size observation and AlexisOlson comment (Abbott-Hare, [Er74d] context,
     non-triviality) accurately reflected.
   - Li [Li25] arXiv:2512.24850: both results (transversal negative deg<=6, chromatic positive
     9-vertex min-deg-7 construction) match DB.
   - ChromaticallyThreeCritical def includes edge-deletion AND vertex-deletion; DB says
     "deleting any edge or vertex" -- faithful.
   - Transversal criticality def (tau=3, edge-deletion has 2-transversal) matches DB's first reading.
   - Fano plane degree example: vertex 0 in {0,1,2},{0,3,4},{0,5,6} = 3 edges. Correct.
   - Fano plane is 3-chromatic and edge-critical: standard, correctly used as satisfiability witness.
-/
