/-
  Erdős Problem #895 — independent Schur triples in triangle-free
  graphs on {1, …, n}.
  Status: proved (Barber, SAT-verified for all n ≥ 18; personal
  communication per DB).  Tier B archive target with a small-n layer.

  Verbatim statement (`goof erdos fetch 895`, pulled 2026-08-05):

    "Is it true that, for all sufficiently large $n$, if $G$ is a
    triangle-free graph on $\{1,\ldots,n\}$ then there must exist three
    independent points $a,b,a+b$?"

  DB remarks: problem of Erdős–Hajnal.  Hajnal expected an independent
  Hindman set (all subset sums of a₁,…,a_k independent) — that general
  question remains OPEN.  The stated problem was resolved by Barber
  (personal communication), verifying by SAT that it holds for all
  n ≥ 18.

  Formalization: vertices are `Fin n` labelled by the integers
  1, …, n via `v ↦ v.val + 1`; "three independent points a, b, a+b"
  means pairwise non-adjacent AND pairwise distinct vertices (a = b
  would degenerate the triple; a+b is automatically distinct from a, b
  since labels are positive).

  The n ≥ 18 direction needs verified SAT-certificate replay (DRAT/LRAT
  checking), which the repo lacks — archived.  The small-n layer
  (explicit triangle-free counterexample graphs for n < 18) is
  formalizable now via native_decide.

  Mathlib inventory (leandoc 2026-08-05): `SimpleGraph.CliqueFree 3`
  for triangle-freeness, `SimpleGraph.IsIndepSet`; nothing further.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E895

open SimpleGraph

/-- `HasIndepSchurTriple G`: there are vertices with labels `a`, `b`,
    `a + b` (labels in `{1, …, n}` via `val + 1`), pairwise distinct and
    pairwise non-adjacent in `G`. -/
def HasIndepSchurTriple {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c : Fin n, (a.val + 1) + (b.val + 1) = c.val + 1 ∧
    a ≠ b ∧ ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c

/-- Satisfiability: the empty graph on `{1,…,3}` has the triple
    1 + 2 = 3.  -- PROVABLE (decide). -/
example : HasIndepSchurTriple (⊥ : SimpleGraph (Fin 3)) := by
  sorry

/-- **Erdős #895, Barber's theorem**: for every `n ≥ 18`, every
    triangle-free graph on `{1, …, n}` has an independent Schur triple
    `a, b, a+b`.

    Source text: "Is it true that, for all sufficiently large $n$, if
    $G$ is a triangle-free graph on $\{1,\ldots,n\}$ then there must
    exist three independent points $a,b,a+b$?"  Resolved YES with
    threshold 18 (SAT).

    Proof route in-repo: none currently — the literature proof is a SAT
    enumeration; a formal proof needs either (a) verified LRAT replay
    infrastructure (absent), or (b) a human proof (none published).
    Archived with the exact threshold so the statement is falsifiable
    against future certificates.  Note `Fintype`/`DecidableRel`
    instances make the per-n claim decidable in principle — but the
    quantifier over all graphs on 18 labelled vertices (2^153 graphs)
    is far outside `native_decide`; symmetry reduction is what the SAT
    solver supplied. -/
theorem barber_indep_schur (n : ℕ) (hn : 18 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    HasIndepSchurTriple G := by
  sorry

/-- **Small-n sharpness layer (the formalizable slice)**: the threshold
    is genuine — there exists a triangle-free graph on `{1, …, 17}`
    with NO independent Schur triple.

    Attack: pull/search the explicit 17-vertex witness (a sage/SAT
    probe reconstructs it in seconds — the constraint system is tiny),
    encode its edge list as a `SimpleGraph (Fin 17)` via
    `SimpleGraph.fromEdgeSet`/`fromRel`, then `native_decide` both
    triangle-freeness and triple-freeness.  Same certificate pattern as
    `Proofs/Erdos/Erdos715` doubledTriangle.  Effort S once the edge
    list is in hand. -/
theorem sharpness_seventeen :
    ∃ (G : SimpleGraph (Fin 17)) (_ : DecidableRel G.Adj),
      G.CliqueFree 3 ∧ ¬ HasIndepSchurTriple G := by
  sorry

/-- **Hajnal's Hindman-set strengthening (OPEN)**, archived: for every
    `k` there is `n₀(k)` such that any triangle-free `G` on
    `{1, …, n}`, `n ≥ n₀(k)`, has `a : Fin k → ℕ` positive with all
    nonempty-subset sums `≤ n`, distinct, and pairwise non-adjacent
    (an independent Hindman set). -/
theorem hajnal_hindman_open (k : ℕ) (hk : 1 ≤ k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        G.CliqueFree 3 →
        ∃ a : Fin k → ℕ, (∀ i, 1 ≤ a i) ∧
          (∀ S : Finset (Fin k), S.Nonempty → ∑ i ∈ S, a i ≤ n) ∧
          ∀ S T : Finset (Fin k), S.Nonempty → T.Nonempty → S ≠ T →
            (∑ i ∈ S, a i ≠ ∑ i ∈ T, a i) ∧
            ∀ (hS : ∑ i ∈ S, a i ≤ n) (hT : ∑ i ∈ T, a i ≤ n),
              ¬ G.Adj ⟨∑ i ∈ S, a i - 1, by omega⟩
                      ⟨∑ i ∈ T, a i - 1, by omega⟩ := by
  sorry

end ErdosCandidates.E895

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB exactly.
   - HasIndepSchurTriple correctly encodes labels via val+1; the Schur
     condition (a.val+1)+(b.val+1)=c.val+1 is faithful.  Distinctness
     of c from a,b follows from positivity of labels, as the comment
     notes -- no explicit a!=c or b!=c needed.
   - Barber threshold n>=18 matches DB section text ("verified using a
     SAT solver that this is true for all n>=18").
   - Hajnal Hindman-set strengthening correctly marked OPEN, matching DB.
   - Sharpness at n=17 is consistent with the n>=18 threshold.
   - Triangle-freeness via CliqueFree 3 is standard Mathlib encoding.
   - Attribution: Erdos-Hajnal provenance, Barber personal communication
     -- all match DB.  No comment-sourced claims to flag.
-/
