/-
  Erdős Problem #901 — Property B and m(n).
  Status: open.  Tier UC lemma mine (m(2) = 3, m(3) = 7 finite
  theorems; union-bound lower bound).

  Verbatim statement (`goof erdos fetch 901`, pulled 2026-08-05):

    "Let $m(n)$ be minimal such that there is an $n$-uniform
    hypergraph with $m(n)$ edges which is $3$-chromatic. Estimate
    $m(n)$."

  DB remarks: 3-chromatic = does not have Property B (no set meets
  every edge without containing one; equivalently not 2-colorable).
  Known: m(2) = 3, m(3) = 7, m(4) = 23.  Erdős: 2ⁿ ≪ m(n) ≪ n²2ⁿ
  ([Er63b], [Er64e]).  Beck [Be77], [Be78]: m(n) ≫ n^{1/3−o(1)}2ⁿ.
  Radhakrishnan–Srinivasan [RaSr00]: m(n) ≫ √(n/log n)·2ⁿ.  Pluhár
  [Pl09]: short proof of m(n) ≫ n^{1/4}2ⁿ.  Erdős–Lovász [ErLo75]
  speculate m(n) ≍ n·2ⁿ.

  Repo adjacency: shares the ProperColoring vocabulary with #836 and
  #834 sketches; `Proofs/Erdos/ErdosLovasz.lean` is the same paper.

  Mathlib inventory: no hypergraph 2-colorability; fresh defs
  (consistent with E836/E834 files).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E901

variable {V : Type*} [DecidableEq V]

/-- `TwoColorable H`: some 2-coloring leaves no edge monochromatic
    (= Property B). -/
def TwoColorable (H : Finset (Finset V)) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ H, (∃ x ∈ e, c x = true) ∧ (∃ x ∈ e, c x = false)

/-- `mProperty n m`: there is an `n`-uniform hypergraph with `m`
    edges (on some finite vertex set, wlog `Fin (n*m)`) that is NOT
    2-colorable. -/
def mProperty (n m : ℕ) : Prop :=
  ∃ H : Finset (Finset (Fin (n * m))),
    H.card = m ∧ (∀ e ∈ H, e.card = n) ∧ ¬ TwoColorable H

/-- `mB n`: the minimal number of edges of a non-2-colorable
    `n`-uniform hypergraph — the `m(n)` of the problem.  `sInf` is
    honest for `n ≥ 1`: the complete `n`-uniform hypergraph on `2n−1`
    vertices is not 2-colorable (any 2-coloring has a color class of
    size ≥ n).  Support `Fin (n*m)` loses no generality: `m` edges of
    size `n` touch ≤ n·m vertices. -/
noncomputable def mB (n : ℕ) : ℕ := sInf {m : ℕ | mProperty n m}

/-- `m(2) = 3`: the triangle {{a,b},{b,c},{a,c}} is not 2-colorable
    (some pair repeats a color), and any 2 edges are 2-colorable.
    -- PROVABLE (decide-scale; the encoding bookkeeping on
    `Fin (2*3)` is the only friction).  The quick first landing. -/
theorem mB_two : mB 2 = 3 := by
  sorry

/-- `m(3) = 7`: the Fano plane is the witness (7 edges, 3-uniform,
    not 2-colorable — cf. the E836 sketch's `fano`); minimality is a
    bounded but genuine finite theorem (every 3-uniform hypergraph
    with ≤ 6 edges is 2-colorable).
    -- PROVABLE (witness by decide; minimality via a bounded search /
    union-bound argument — Effort M, flagged as nontrivial). -/
theorem mB_three : mB 3 = 7 := by
  sorry

/-- `m(4) = 23` (Östergård's computation, reported in the DB): the
    heavy certified-search boundary; archived. -/
theorem mB_four : mB 4 = 23 := by
  sorry

/-- **Union-bound lower bound (the entry-point target)**:
    `2^{n-1} < m(n)` — a hypergraph with `m ≤ 2^{n-1}` edges is
    2-colorable.  Finite probabilistic argument: a uniformly random
    2-coloring makes each edge monochromatic with probability
    `2^{1-n}`; with `m ≤ 2^{n-1}` edges the expected number of
    monochromatic edges is ≤ 1, and strict inequality analysis (or
    the weighted counting over all 2^V colorings) yields a proper
    coloring.  Fully finite: count colorings, no measure theory.
    This is Erdős's [Er63b] bound; next door to the repo's
    ErdosLovasz counting style.  Effort M. -/
theorem union_bound_lower (n : ℕ) (hn : 2 ≤ n) : 2 ^ (n - 1) < mB n := by
  sorry

/-- **Erdős's upper bound** ([Er64e]), archived: `m(n) ≪ n²·2ⁿ` —
    random construction.  Stated with explicit constant. -/
theorem erdos_upper :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → mB n ≤ C * n ^ 2 * 2 ^ n := by
  sorry

/-- **Radhakrishnan–Srinivasan** ([RaSr00]), archived:
    `m(n) ≫ √(n/log n)·2ⁿ`. -/
theorem radhakrishnan_srinivasan :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.sqrt (n / Real.log n) * 2 ^ n ≤ (mB n : ℝ) := by
  sorry

/-- Satisfiability sanity: the triangle (as 2-uniform hypergraph on 3
    vertices, embedded in `Fin 6`) is not 2-colorable.
    -- PROVABLE (decide). -/
example : ¬ TwoColorable
    ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 6))) := by
  sorry

end ErdosCandidates.E901

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB: "m(n) minimal ... n-uniform ... 3-chromatic."
   - DB values m(2)=3, m(3)=7, m(4)=23 match file theorems.
   - Bounds: 2^n << m(n) << n^2*2^n (Erdos), sqrt(n/log n)*2^n (R-S) match DB.
   - Erdos-Lovasz n*2^n speculation recorded in file header, matches DB.
   - Triangle non-2-colorability: triangle is odd cycle on 3 vertices, not
     2-colorable as a 2-uniform hypergraph (each edge needs both colors). Correct.
   - TwoColorable def correctly captures Property B; mProperty/mB correctly
     capture the negation. Lean types faithful.
   - union_bound_lower states 2^(n-1) < mB n, consistent with the standard
     first-moment bound from [Er63b].
-/
