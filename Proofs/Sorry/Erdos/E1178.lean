/-
  Erdős Problem #1178 — the Brown–Erdős–Sós conjecture.
  Status: open.  Tier UC lemma mine (the BES lower-bound
  construction).

  Verbatim statement (`goof erdos fetch 1178`, pulled 2026-08-05):

    "For $r\geq 3$ let $d_r(e)$ be the minimal $d$ such that
    \[\mathrm{ex}_r(n,\mathcal{F})=o(n^2),\]
    where $\mathcal{F}$ is the family of $r$-uniform hypergraphs on
    $d$ vertices with $e$ edges.

    Prove that\[d_r(e)=(r-2)e+3\]for all $r,e\geq 3$."

  DB remarks: BES73 proved d_r(e) ≥ (r−2)e + 3.  Ruzsa–Szemerédi
  [RuSz78]: d_3(3) = 6 (the (6,3) theorem).  Erdős–Frankl–Rödl
  [EFR86]: d_r(3) = 3(r−2) + 3 = 3r − 3 for all r.  Sárközy–Selkow:
  d_r(e) ≤ (r−2)e + 2 + ⌊log₂ e⌋.  Conlon–Gishboliner–Levanzov–
  Shapira [CGLS23]: d_3(e) ≤ e + O(log e / log log e).

  Audit verdict: the equality direction runs through
  regularity/removal — out of reach; the mine is the BES73
  lower-bound construction (finite hypergraph combinatorics).

  Mathlib inventory: no hypergraph Turán machinery; the `exr` def
  below is the small fresh layer ("`ex_r` Turán-density defs" from
  the candidates doc).  Sub-hypergraph containment via injections.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1178

/-- `ContainsCopy H d e`: the `r`-uniform edge family `H` on vertex
    type `V` contains an injective copy of SOME `d`-vertex,
    `e`-edge configuration — i.e. there are `e` distinct edges of `H`
    spanning at most `d` vertices.  (This "≤ d vertices, e edges"
    reading is exactly membership of some member of the family
    `𝓕(d, e)` of the problem.) -/
def ContainsConfig {V : Type*} [DecidableEq V] (H : Finset (Finset V))
    (d e : ℕ) : Prop :=
  ∃ S ⊆ H, S.card = e ∧ (S.sup id).card ≤ d

/-- `exr n r d e`: the Turán number — the maximal number of edges of
    an `r`-uniform hypergraph on `Fin n` containing no `(d, e)`
    configuration. -/
open scoped Classical in
noncomputable def exr (n r d e : ℕ) : ℕ :=
  Finset.sup
    ((((Finset.univ : Finset (Fin n)).powersetCard r).powerset).filter
      (fun H => ¬ ContainsConfig H d e))
    Finset.card

/-- Ground truth ((6,3)-shape): a 3-uniform hypergraph with 3 edges
    on ≤ 6 vertices is exactly the forbidden configuration of the
    Ruzsa–Szemerédi theorem; e.g. {123, 345, 561} has 3 edges on 6
    vertices — witnesses `ContainsConfig` itself.
    -- PROVABLE (decide). -/
example : ContainsConfig
    ({{0,1,2}, {2,3,4}, {4,5,0}} : Finset (Finset (Fin 6))) 6 3 := by
  sorry

/-- **Erdős #1178, the Brown–Erdős–Sós conjecture (OPEN)**:
    `d_r(e) = (r−2)e + 3` — stated as the two-sided quantitative
    form: for `d = (r−2)e + 3` the Turán number is `o(n²)`
    (the OPEN upper direction), while for `d = (r−2)e + 2` it is
    `≫ n²` (the BES lower construction, a theorem).  Upper (open)
    direction: -/
theorem bes_conjecture_upper (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (exr n r ((r - 2) * e + 3) e : ℝ) ≤ ε * n ^ 2 := by
  sorry

/-- **BES73 lower bound (the lemma-mine target)**: with
    `d = (r−2)e + 2` the Turán number is `≫ n²` — there are
    `r`-uniform hypergraphs with `c·n²` edges and no `e` edges on
    `(r−2)e + 2` vertices.  The construction is finite combinatorics
    (partite blow-ups of a partial Steiner system); in the repo's
    existing `Finset (Finset _)` vocabulary.  Effort M. -/
theorem bes_lower_bound (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * n ^ 2 ≤ (exr n r ((r - 2) * e + 2) e : ℝ) := by
  sorry

/-- **Ruzsa–Szemerédi (6,3) theorem** ([RuSz78]), archived:
    `d_3(3) = 6`, i.e. 3-uniform hypergraphs with no 3 edges on ≤ 6
    vertices have `o(n²)` edges.  The proof runs through the triangle
    removal lemma — Mathlib HAS Szemerédi regularity and triangle
    removal (`Mathlib.Combinatorics.SimpleGraph.Regularity.*`,
    `triangle_removal`), so this is a heavy-but-conceivable bridge
    target. -/
theorem ruzsa_szemeredi (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (exr n 3 6 3 : ℝ) ≤ ε * n ^ 2 := by
  sorry

/-- **Sárközy–Selkow upper bound** ([SaSe05]), archived:
    `d_r(e) ≤ (r−2)e + 2 + ⌊log₂ e⌋` — with that many allowed
    vertices, the Turán number is `o(n²)`. -/
theorem sarkozy_selkow (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (exr n r ((r - 2) * e + 2 + Nat.log 2 e) e : ℝ) ≤ ε * n ^ 2 := by
  sorry

end ErdosCandidates.E1178

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB: d_r(e) = (r-2)e+3 for r,e >= 3.
   - BES73 lower bound d_r(e) >= (r-2)e+3 matches DB.
   - Ruzsa-Szemeredi d_3(3) = 6 matches DB.
   - Sarkozy-Selkow d_r(e) <= (r-2)e+2+floor(log2 e) matches DB.
   - CGLS23 d_3(e) <= e+O(log e / log log e) matches DB.
   - EFR86 d_r(3) = 3(r-2)+3 = 3r-3 matches DB (stated as (r-2)3+3).
   - BES lower bound theorem uses d = (r-2)e+2 (one less than the threshold),
     and the upper conjecture uses d = (r-2)e+3. Correct two-sided split.
   - Ground truth example: 3 edges on 6 vertices, 3-uniform. Correct.
   - Lean types faithful to the mathematical content.
-/
