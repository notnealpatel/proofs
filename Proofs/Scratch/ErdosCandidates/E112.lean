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
  Steiner have a simple argument giving exactly k(n,m) = (n−1)(m−1)
  — wait, the DB says (n−1)(m−1) for the path variant: the exact
  self-contained slice.

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

/-- `TransTournamentOn r S`: `r` restricted to `S` is a transitive
    tournament — some linear order of `S` realizes all forward arcs.
    Encoded via an order-embedding of `Fin S.card`… concretely: an
    injection `e : Fin s ↪ V` with image `S` and `r (e i) (e j)` for
    all `i < j`. -/
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

/-- Ground truth at the trivial boundary: `k(n, 1) = 0`? A transitive
    tournament of size 1 is a single vertex — any nonempty digraph has
    one, and the empty digraph (N = 0) has none, and also no
    independent 1-set...  `RamseyDigraph 0 n 1` is FALSE for n ≥ 1
    (both disjuncts need a vertex), while `RamseyDigraph 1 n 1` holds.
    So `kDigraph n 1 = 1` for `n ≥ 1`.  Pins the size conventions.
    -- PROVABLE (decide-scale logic). -/
example : kDigraph 2 1 = 1 := by
  sorry

/-- Ground truth, first nontrivial diagonal: `k(2,2)`: every digraph
    on N vertices has 2 independent vertices or an arc (a transitive
    2-tournament).  Any digraph on 2 vertices: either some arc (T₂) or
    none (independent pair) — so `k(2,2) = 2`.
    -- PROVABLE. -/
example : kDigraph 2 2 = 2 := by
  sorry

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

/-- **The Hunter–Steiner path variant (the provable slice)**: with
    "transitive tournament" replaced by "directed path on m vertices"
    (consecutive arcs only), the threshold is exactly `(n−1)(m−1)+1`…
    the DB states the answer as k = (n−1)(m−1) — pin the off-by-one
    against their argument during proof; we state the two directions
    separately with the DB's value.

    `DirPathOn r m S`: an injection realizing arcs along consecutive
    indices. -/
def DirPathOn (r : V → V → Prop) (s : ℕ) (S : Finset V) : Prop :=
  ∃ e : Fin s ↪ V, (∀ i, e i ∈ S) ∧ S.card = s ∧
    ∀ i : ℕ, ∀ h : i + 1 < s,
      r (e ⟨i, by omega⟩) (e ⟨i + 1, h⟩)

/-- Hunter–Steiner, path variant, exact value (DB: "a simple argument
    that proves, for this alternative definition, that
    k(n,m) = (n−1)(m−1)").  Self-contained; the argument is a
    Dilworth/Mirsky-style layering — Mathlib has
    `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` and the
    Mirsky/Dilworth machinery (`Mathlib/Order/Antichain`,
    `Mathlib/Combinatorics/Dilworth`? re-probe leandoc).  Effort M;
    genuinely landable. -/
theorem hunter_steiner_path_exact (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    sInf {N : ℕ | ∀ r : Fin N → Fin N → Prop, (∀ v, ¬ r v v) →
        (∃ S : Finset (Fin N), S.card = n ∧ IndepSet r S) ∨
        (∃ S : Finset (Fin N), DirPathOn r m S)} =
      (n - 1) * (m - 1) := by
  sorry

end ErdosCandidates.E112

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - Verbatim statement matches `goof erdos fetch 112` exactly.
   - Erdos-Rado bound: DB says k(n,m) <= (2^{m-1}(n-1)^m + n - 2)/(2n-3). File's
     denominator-cleared form (2n-3)*k(n,m) <= 2^{m-1}(n-1)^m + n - 2 is algebraically
     equivalent. Correct.
   - Larson-Mitchell k(n,3) <= n^2: matches DB.
   - kDigraph 2 1 = 1 verified: RamseyDigraph 1 2 1 holds (singleton is a 1-tournament),
     RamseyDigraph 0 2 1 fails (no vertices). Correct.
   - kDigraph 2 2 = 2 verified: on Fin 2 any irreflexive r yields an arc or an independent
     pair; on Fin 1 neither disjunct holds. Correct.
   - FLAG (Hunter-Steiner path value): DB states k(n,m) = (n-1)(m-1) for the path variant.
     File transcribes this faithfully. However, at n=2, m=2 this gives 1, but path-k(2,2)=2
     (on 1 vertex neither an independent 2-set nor a directed 2-path exists). The file header
     already flags this ("pin the off-by-one"), suggesting awareness. The correct formula may
     be (n-1)(m-1)+1. Recommend resolving by fetching the Hunter-Steiner argument before
     attempting the proof.
   - No Mathlib tournament or digraph-Ramsey defs found (confirmed by grep).
-/
