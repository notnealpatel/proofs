/-
  Erdős Problem #112 — independent sets versus transitive
  subtournaments in digraphs.
  Status: open.  Tier C infrastructure target (tournament layer).

  Verbatim statement (`goof erdos fetch 112`, pulled 2026-08-05):

    "Let $k=k(n,m)$ be minimal such that any directed graph on $k$
    vertices must contain either an independent set of size $n$ or a
    transitive tournament of size $m$. Determine $k(n,m)$."

  DB remarks (Erdős–Rado [ErRa67]): k(n,m) ≤
  (2^{m-1}(n-1)^m + n - 2)/(2n - 3).  Larson–Mitchell [LaMi97]:
  k(n,3) ≤ n².  Zach Hunter: R(n,m) ≤ k(n,m) ≤ R(n,m,m), so
  k(n,m) ≤ 3^{n+2m}.  The graphs-collection variant replaces
  transitive tournament by directed path; for THAT variant Hunter and
  Steiner have a simple argument giving the vertex-count threshold
  k(n,m) = (n−1)(m−1)+1. The quoted DB value without +1 is not the
  vertex-count threshold: n=m=2 requires two vertices, not one.

  Formalization: a "directed graph" here allows any irreflexive
  relation (edges may go both ways? For Erdős–Rado partition-relation
  provenance the digraph is an arbitrary irreflexive relation;
  independent = no arc either way; transitive tournament = linearly
  ordered subset with all forward arcs).  We use `r : V → V → Prop`
  irreflexive.

  Mathlib inventory (leandoc 2026-08-05): no tournament type
  (leandoc miss "Tournament"); `Digraph` exists in Mathlib
  (Combinatorics/Digraph/Basic) but carries no irreflexivity;
  the ~100-line layer here is the infrastructure contribution.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E112

variable {V : Type*}

/-- `IndepSet r S`: no arc of `r` joins two members of `S` (in either
    direction). -/
def IndepSet (r : V → V → Prop) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ r a b

/-- `TransTournamentOn r s S`: `S` contains a NON-INDUCED transitive
    tournament subgraph on `s` vertices. An injection enumerates `S` and
    requires all forward arcs. Reverse ambient arcs are allowed; the ambient
    digraph need not be a tournament. No induced iff condition is asserted. -/
def TransTournamentOn (r : V → V → Prop) (s : ℕ) (S : Finset V) : Prop :=
  ∃ e : Fin s ↪ V, (∀ i, e i ∈ S) ∧ S.card = s ∧
    ∀ i j : Fin s, i < j → r (e i) (e j)

/-- `RamseyDigraph N n m`: every irreflexive digraph on `N` vertices
    contains an independent `n`-set or a transitive tournament on `m`
    vertices. -/
def RamseyDigraph (N n m : ℕ) : Prop :=
  ∀ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) →
    (∃ S : Finset (Fin N), S.card = n ∧ IndepSet r S) ∨
    (∃ S : Finset (Fin N), TransTournamentOn r m S)

/-- `kDigraph n m`: the minimal such `N` — the `k(n,m)` of the
    problem.  Nonemptiness of the defining set is the Erdős–Rado
    bound (archived below), so `sInf` is honest modulo that input. -/
noncomputable def kDigraph (n m : ℕ) : ℕ := sInf {N : ℕ | RamseyDigraph N n m}

/-- Any qualifying vertex count is at least the smaller requested size. -/
private theorem min_le_of_ramsey (N n m : ℕ) (h : RamseyDigraph N n m) :
    min n m ≤ N := by
  obtain hind | htour := h (fun _ _ => False) (by simp)
  · obtain ⟨S, hcard, _⟩ := hind
    have hn : n ≤ N := by simpa [hcard] using Finset.card_le_univ S
    exact (min_le_left n m).trans hn
  · obtain ⟨S, e, _, hcard, _⟩ := htour
    have hm : m ≤ N := by simpa [hcard] using Finset.card_le_univ S
    exact (min_le_right n m).trans hm

/-- A single vertex contains a transitive tournament of size one. -/
private theorem ramsey_one_two_one : RamseyDigraph 1 2 1 := by
  intro r hirr
  right
  refine ⟨{0}, Function.Embedding.refl _, ?_, ?_, ?_⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi]
  · simp
  · intro i j hij
    have heq : i = j := Subsingleton.elim _ _
    exact False.elim ((ne_of_lt hij) heq)

/-- Two vertices either have an arc or form an independent pair. -/
private theorem ramsey_two_two_two : RamseyDigraph 2 2 2 := by
  intro r hirr
  classical
  by_cases h01 : r 0 1
  · right
    refine ⟨Finset.univ, Function.Embedding.refl _, ?_, ?_, ?_⟩
    · intro i
      exact Finset.mem_univ _
    · simp
    · intro i j hij
      have hi : i = 0 := by fin_cases i <;> fin_cases j <;> simp_all
      have hj : j = 1 := by fin_cases i <;> fin_cases j <;> simp_all
      simpa [hi, hj] using h01
  · by_cases h10 : r 1 0
    · right
      refine ⟨Finset.univ, (Equiv.swap (0 : Fin 2) 1).toEmbedding, ?_, ?_, ?_⟩
      · intro i
        exact Finset.mem_univ _
      · simp
      · intro i j hij
        have hi : i = 0 := by fin_cases i <;> fin_cases j <;> simp_all
        have hj : j = 1 := by fin_cases i <;> fin_cases j <;> simp_all
        simpa [hi, hj] using h10
    · left
      refine ⟨Finset.univ, by simp, ?_⟩
      intro a ha b hb
      fin_cases a <;> fin_cases b
      · exact hirr 0
      · exact h01
      · exact h10
      · exact hirr 1

/-- Ground truth at the singleton boundary: `k(2,1) = 1`. -/
theorem kDigraph_two_one : kDigraph 2 1 = 1 := by
  have hmem : 1 ∈ {N : ℕ | RamseyDigraph N 2 1} := ramsey_one_two_one
  have hnonempty : Set.Nonempty {N : ℕ | RamseyDigraph N 2 1} := ⟨1, hmem⟩
  have hupper : kDigraph 2 1 ≤ 1 := Nat.sInf_le hmem
  have hramsey : RamseyDigraph (kDigraph 2 1) 2 1 := Nat.sInf_mem hnonempty
  have hlower := min_le_of_ramsey _ _ _ hramsey
  simpa using Nat.le_antisymm hupper hlower

/-- Ground truth at the first diagonal: `k(2,2) = 2`. -/
theorem kDigraph_two_two : kDigraph 2 2 = 2 := by
  have hmem : 2 ∈ {N : ℕ | RamseyDigraph N 2 2} := ramsey_two_two_two
  have hnonempty : Set.Nonempty {N : ℕ | RamseyDigraph N 2 2} := ⟨2, hmem⟩
  have hupper : kDigraph 2 2 ≤ 2 := Nat.sInf_le hmem
  have hramsey : RamseyDigraph (kDigraph 2 2) 2 2 := Nat.sInf_mem hnonempty
  have hlower := min_le_of_ramsey _ _ _ hramsey
  simpa using Nat.le_antisymm hupper hlower

example : RamseyDigraph 1 2 1 := ramsey_one_two_one
example : RamseyDigraph 2 2 2 := ramsey_two_two_two

/-- **Erdős #112 (OPEN)**: determine `k(n,m)`.  Archived via the known
    bounds; the determination question has no closed form conjectured
    in the DB.  **Erdős–Rado upper bound** ([ErRa67]), stated
    denominator-cleared: `(2n−3)·k(n,m) ≤ 2^{m−1}(n−1)^m + n − 2`
    (for n, m ≥ 2). -/
theorem erdos_rado_upper (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (2 * n - 3) * kDigraph n m ≤ 2 ^ (m - 1) * (n - 1) ^ m + n - 2 := by
  sorry

/-- **Larson–Mitchell** ([LaMi97]), archived: `k(n,3) ≤ n²`. -/
theorem larson_mitchell (n : ℕ) (hn : 2 ≤ n) :
    kDigraph n 3 ≤ n ^ 2 := by
  sorry

/-- A directed path on `s` vertices in `S`, given by an injection realizing
    consecutive forward arcs. Extra ambient arcs are allowed. -/
def DirPathOn (r : V → V → Prop) (s : ℕ) (S : Finset V) : Prop :=
  ∃ e : Fin s ↪ V, (∀ i, e i ∈ S) ∧ S.card = s ∧
    ∀ i : ℕ, ∀ h : i + 1 < s,
      r (e ⟨i, by omega⟩) (e ⟨i + 1, h⟩)

/-- Hunter–Steiner path variant: the vertex-count threshold is
    `(n-1)*(m-1)+1`, so n=m=2 gives 2. Retained as an admission.

    Prose justification only: the lower construction is the disjoint union
    of (n-1) bidirected cliques of size (m-1); it has neither an independent
    n-set nor a directed path on m vertices. The upper argument uses the
    directed-path/chromatic bound and the independence bound from a coloring.
    This does not claim induced and non-induced extremal functions coincide. -/
theorem hunter_steiner_path_exact (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    sInf {N : ℕ | ∀ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) →
        (∃ S : Finset (Fin N), S.card = n ∧ IndepSet r S) ∨
        (∃ S : Finset (Fin N), DirPathOn r m S)} =
      (n - 1) * (m - 1) + 1 := by
  sorry

end ErdosCandidates.E112

/- AMENDED REVIEW
   The previous path-value transcription is not a correct vertex threshold.
   hunter_steiner_path_exact now has the +1 boundary correction and remains
   admitted. TransTournamentOn has the non-induced forward-arc meaning;
   reverse arcs are permitted. No equivalence with an induced extremal
   function is asserted. The other relation definitions and statements are
   unchanged. The lower construction and chromatic upper argument above are
   prose justification, not a new formal proof.
-/
