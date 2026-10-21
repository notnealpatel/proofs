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
example : HasIndepSchurTriple (⊥ : SimpleGraph (Fin 3)) :=
  ⟨0, 1, 2, rfl, by decide, by simp, by simp, by simp⟩

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

/-- Neighbour bitmasks of the 17-vertex witness, 0-based: bit `j` of
    `nbrMask17 i` is set iff vertices with labels `i + 1` and `j + 1` are
    adjacent.  Edge list (1-based labels): (1,3),(1,5),(1,10),(1,12),
    (1,14),(1,16),(2,5),(2,6),(2,9),(2,12),(2,13),(2,16),(3,7),(3,9),
    (3,11),(3,13),(3,15),(4,9),(4,10),(4,11),(4,12),(5,8),(5,11),(5,15),
    (6,7),(6,10),(6,14),(6,15),(7,8),(7,12),(7,16),(8,9),(8,10),(9,14),
    (10,17),(11,17),(12,17),(13,17),(14,17),(15,17),(16,17). -/
private def nbrMask17 (i : ℕ) : ℕ :=
  [43540, 39216, 21825, 3840, 17539, 25154, 34980, 848, 8334, 65705, 65564, 65611,
    65542, 65825, 65588, 65603, 65024].getD i 0

/-- Boolean adjacency of the witness on 0-based indices. -/
private def adj17 (i j : ℕ) : Bool := (nbrMask17 i).testBit j

/-- Ground truth: labels 1 and 3 are adjacent, labels 1 and 2 are not. -/
example : adj17 0 2 = true ∧ adj17 0 1 = false := by decide

/-- Kernel certificate: the symmetrised witness relation has no triangle
    (all triples of indices `< 17`, equal ones included). -/
private theorem triangle_cert17 : ∀ a < 17, ∀ b < 17, ∀ c < 17,
    ((adj17 a b || adj17 b a) && (adj17 a c || adj17 c a) &&
      (adj17 b c || adj17 c b)) = false := by
  decide

/-- Kernel certificate: for distinct indices `a, b` with `a + b + 1 < 17`
    (labels `a+1`, `b+1`, `a+b+2`), some pair of the triple is adjacent. -/
private theorem schur_cert17 : ∀ a < 17, ∀ b < 17, a ≠ b → a + b + 1 < 17 →
    ((adj17 a b || adj17 b a) || (adj17 a (a + b + 1) || adj17 (a + b + 1) a) ||
      (adj17 b (a + b + 1) || adj17 (a + b + 1) b)) = true := by
  decide

/-- The 17-vertex triangle-free witness graph (SAT witness). -/
private def G17 : SimpleGraph (Fin 17) :=
  SimpleGraph.fromRel fun a b => adj17 a.val b.val = true

/-- Adjacency in `G17` implies the symmetrised Boolean relation. -/
private theorem G17_adj_imp {a b : Fin 17} (h : G17.Adj a b) :
    (adj17 a.val b.val || adj17 b.val a.val) = true := by
  rw [G17, SimpleGraph.fromRel_adj] at h
  simpa only [Bool.or_eq_true] using h.2

/-- Distinct vertices related by the symmetrised Boolean relation are
    adjacent in `G17`. -/
private theorem G17_adj_of {a b : Fin 17} (hne : a ≠ b)
    (h : (adj17 a.val b.val || adj17 b.val a.val) = true) : G17.Adj a b := by
  rw [G17, SimpleGraph.fromRel_adj]
  exact ⟨hne, by simpa only [Bool.or_eq_true] using h⟩

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
  refine ⟨G17, Classical.decRel _, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 ht
    have hcert := triangle_cert17 a.val a.isLt b.val b.isLt c.val c.isLt
    rw [G17_adj_imp hab, G17_adj_imp hac, G17_adj_imp hbc] at hcert
    exact absurd hcert (by decide)
  · rintro ⟨a, b, c, hsum, hab, hnab, hnac, hnbc⟩
    have hc : c.val = a.val + b.val + 1 := by omega
    have hcert := schur_cert17 a.val a.isLt b.val b.isLt (Fin.val_ne_of_ne hab) (hc ▸ c.isLt)
    rw [← hc] at hcert
    have hac : a ≠ c := fun h => by rw [h] at hc; omega
    have hbc : b ≠ c := fun h => by rw [h] at hc; omega
    simp only [Bool.or_eq_true] at hcert
    rcases hcert with (h | h) | h
    · exact hnab (G17_adj_of hab (by simpa only [Bool.or_eq_true] using h))
    · exact hnac (G17_adj_of hac (by simpa only [Bool.or_eq_true] using h))
    · exact hnbc (G17_adj_of hbc (by simpa only [Bool.or_eq_true] using h))

/-- **Hajnal's Hindman-set strengthening (OPEN)**, archived: for every
    `k` there is `n₀(k)` such that any triangle-free `G` on
    `{1, …, n}`, `n ≥ n₀(k)`, has `a : Fin k → ℕ` positive with all
    nonempty-subset sums `≤ n`, distinct, and pairwise non-adjacent
    (an independent Hindman set).  The positivity hypothesis is bound as a
    dependent existential so the vertex bounds can be discharged inside
    the statement. -/
theorem hajnal_hindman_open (k : ℕ) (hk : 1 ≤ k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        G.CliqueFree 3 →
        ∃ a : Fin k → ℕ, ∃ ha : ∀ i, 1 ≤ a i,
          (∀ S : Finset (Fin k), S.Nonempty → ∑ i ∈ S, a i ≤ n) ∧
          ∀ S T : Finset (Fin k), ∀ hSne : S.Nonempty, ∀ hTne : T.Nonempty, S ≠ T →
            (∑ i ∈ S, a i ≠ ∑ i ∈ T, a i) ∧
            ∀ (hS : ∑ i ∈ S, a i ≤ n) (hT : ∑ i ∈ T, a i ≤ n),
              ¬ G.Adj ⟨∑ i ∈ S, a i - 1,
                        Nat.sub_one_lt_of_le (Finset.sum_pos (fun i _ => ha i) hSne) hS⟩
                      ⟨∑ i ∈ T, a i - 1,
                        Nat.sub_one_lt_of_le (Finset.sum_pos (fun i _ => ha i) hTne) hT⟩ := by
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
